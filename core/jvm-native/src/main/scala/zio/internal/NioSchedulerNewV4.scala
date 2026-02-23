/*
 * Copyright 2021-2024 John A. De Goes and the ZIO Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


package zio.internal

import zio._
import zio.stacktracer.TracingImplicits.disableAutoTrace

import java.util.concurrent.atomic.{AtomicInteger, AtomicLong}
import java.util.concurrent.locks.LockSupport
import java.util.concurrent.{ConcurrentLinkedQueue, ThreadLocalRandom}
import scala.collection.mutable
import scala.concurrent.{BlockContext, CanAwait}

private final class NioScheduler(autoBlocking: Boolean) extends Executor { parent =>

    import Trace.{empty => emptyTrace}
    import NioScheduler.{poolSize, workerOrNull}

    private[this] val globalQueue     = new PartitionedLinkedQueue[Runnable](poolSize * 4)
    private[this] val cache           = new ConcurrentLinkedQueue[NioScheduler.Worker]()
    private[this] val idle            = new ConcurrentLinkedQueue[NioScheduler.Worker]()
    private[this] val globalLocations = makeLocations()
    private[this] val state           = new AtomicInteger(poolSize << 16)
    private[this] val workers         = Array.ofDim[NioScheduler.Worker](poolSize)

    @volatile private[this] var blockingLocations: Set[Trace] = Set.empty

    (0 until poolSize).foreach { workerId =>
        val worker = makeWorker()
        worker.setName(workerId)
        worker.setDaemon(true)
        workers(workerId) = worker
    }
    workers.foreach(_.start())

    if (autoBlocking) {
        val supervisor = makeSupervisor()
        supervisor.setName("NioScheduler-Supervisor")
        supervisor.setDaemon(true)
        supervisor.start()
    }

    override private[zio] def isCurrentThreadInExecutor: Boolean =
        Thread.currentThread().isInstanceOf[NioScheduler.Worker]
    
    def metrics(implicit unsafe: Unsafe): Option[ExecutionMetrics] = {
        val metrics = new ExecutionMetrics {
            def capacity: Int = Int.MaxValue
            def concurrency: Int = poolSize

            def dequeuedCount: Long = {
                var dequeued = 0L
                var i        = 0
                while (i != poolSize) {
                    val worker = workers(i)
                    dequeued += worker.opCount
                    i += 1
                }
                dequeued
            }

            def enqueuedCount: Long = {
                var enqueued = 0L
                var i        = 0
                while (i != poolSize) {
                    val worker = workers(i)
                    enqueued += worker.opCount
                    enqueued += worker.localQueue.size()
                    if (worker.nextRunnable ne null) enqueued += 1
                    i += 1
                }
                enqueued += globalQueue.size()
                enqueued
            }

            def size: Int = {
                var i    = 0
                var size = 0
                while (i != poolSize) {
                    val worker = workers(i)
                    size += worker.localQueue.size()
                    if (worker.nextRunnable ne null) size += 1
                    i += 1
                }

                size += globalQueue.size()
                size
            }

            def workersCount: Int = {
                val currentState = state.get

                (currentState & 0xffff0000) >> 16
            }
        }

        Some(metrics)
    }

    private[this] def makeSupervisor(): NioScheduler.Supervisor =
        new NioScheduler.Supervisor {
            private def countSubmittedAt(location: Trace): Long = {
                var count = globalLocations.get(location)
                var i     = 0
                while (i < poolSize) {
                    val workerCount = workers(i).submittedLocations.get(location)
                    count += workerCount
                    i += 1
                }

                count
            }
            
            override def run(): Unit = {
                val identifiedLocations = makeLocations()
                val previousOpCounts    = Array.fill(poolSize)(-1L)
                while (!isInterrupted) {
                    var workerId = 0
                    while (workerId < poolSize) {
                        val currentWorker = workers(workerId)
                        if (currentWorker.active) {
                            val currentOpCount  = currentWorker.opCount
                            val previousOpCount = previousOpCounts(workerId)
                            if (currentOpCount == previousOpCount) {
                                val currentRunnable = currentWorker.currentRunnable
                                if (currentRunnable.isInstanceOf[FiberRunnable]) {
                                    val fiberRunnable = currentRunnable.asInstanceOf[FiberRunnable]
                                    val location      = fiberRunnable.location
                                    if (location ne emptyTrace) {
                                        val identifiedCount = identifiedLocations.put(location)
                                        val submittedCount  = countSubmittedAt(location)
                                        if (submittedCount > 64 && identifiedCount >= submittedCount / 2) {
                                            blockingLocations += location
                                        }
                                    }
                                }
                                previousOpCounts(workerId) = -1L
                                currentWorker.markAsBlocking()
                            } else {
                                previousOpCounts(workerId) = currentOpCount
                            }
                        } else {
                            previousOpCounts(workerId) = -1L
                        }
                        workerId += 1
                    }

                    val deadline = java.lang.System.currentTimeMillis() + 100
                    var loop     = true
                    while (loop) {
                        LockSupport.parkUntil(deadline)
                        loop = java.lang.System.currentTimeMillis() < deadline
                    }
                }
            }
        }
}

private object NioScheduler {
    private val poolSize = java.lang.Runtime.getRuntime.availableProcessors
    
    def markCurrentWorkerAsBlocking(): Unit = {
        val worker = workerOrNull()
        if (worker ne null) {
            worker.markAsBlocking()
        } else {
            ()
        }
    }

    private def workerOrNull(): NioScheduler.Worker = 
        Thread.currentThread() match {
            case w: NioScheduler.Worker => w
            case _                      => null
        }
    
    private sealed abstract class Locations {
        def get(trace: Trace): Long
        def put(trace: Trace): Long
    }

    private object Locations {
        final class Enabled(sizeHint: Int = 64) extends Locations {
            private[this] val locations = mutable.HashMap.empty[Trace, AtomicLong]
            locations.sizeHint(sizeHint)

            def get(trace: Trace): Long = {
                val v = locations.getOrElse(trace, null)
                if (v eq null) 0L else v.get()
            }

            def put(trace: Trace): Long =
                locations.getOrElseUpdate(trace, new AtomicLong(0L)).getAndIncrement()
        }

        object Disabled extends Locations {
            def get(trace: Trace): Long = 0L
            def put(trace: Trace): Long = 0L
        }
    }

    private sealed abstract class Supervisor extends Thread

    private sealed abstract class Worker extends Thread with BlockContext {
        val submittedLocations: Locations

        @volatile var action: Boolean = true

        @volatile var currentRunnable: Runnable = null
        
        val localQueue: RingBufferPow2[Runnable] = RingBufferPow2[Runnable](256)

        var nextRunnable: Runnable = null

        @volatile var opCount: Long = 0L

        def markAsBlocking(): Unit

        final def setName(i: Int): Unit = setName(s"NioScheduler-Worker-$i")

        override def blockOn[T](thunk: => T)(implicit permission: CanAwait): T = {
            markAsBlocking()
            thunk
        }
    }
}