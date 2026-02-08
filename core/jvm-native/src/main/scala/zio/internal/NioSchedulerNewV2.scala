package zio.internal

import zio._
import zio.stacktracer.TracingImplicits.disableAutoTrace

import java.util.concurrent.atomic.{AtomicInteger, AtomicLong}
import java.util.concurrent.locks.LockSupport
import java.util.concurrent.{ConcurrentLinkedQueue, ThreadLocalRandom}
import scala.collection.mutable
import scala.concurrent.{BlockContext, CanAwait}

import java.util.concurrent.ConcurrentHashMap


/**
- CPU topology: NUMA
- Hyper-threading
- Multicore cache behavior : cache coherance
*/

private final class NioScheduler(autoBlocking: Boolean) extends Executor { parent =>
    
    import Trace.{empty => emptyTrace}
    import NioScheduler.{poolSize, workerOrNull, WorkerActivityTracker}

    private[this] val globalQueue     = new PartitionedLinkedQueue[Runnable](poolSize * 4)
    private[this] val cache           = new ConcurrentLinkedQueue[NioScheduler.Worker]()
    private[this] val idle            = new ConcurrentLinkedQueue[NioScheduler.Worker]()
    private[this] val globalLocations = makeLocations()
    private[this] val state           = new AtomicInteger(poolSize << 16)
    private[this] val workers         = Array.ofDim[NioScheduler.Worker](poolSize)
    private[this] val workersActiveTracker = new WorkerActivityTracker(poolSize)

    @volatile private[this] var blockingLocations: Set[Trace] = Set.empty

    (0 until poolSize).foreach { workerId =>
        val worker = makeWorker()
        worker.setName(workerId)
        worker.setDaemon(true)
        workers(workerId) = worker
        workersActiveTracker.touch(worker)
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

    private[this] def makeLocations(): NioScheduler.Locations =
        if (autoBlocking) new NioScheduler.Locations.Enabled
        else NioScheduler.Locations.Disabled
    
    private[this] def isBlocking(worker: NioScheduler.Worker, runnable: Runnable): Boolean =
        if (autoBlocking && runnable.isInstanceOf[FiberRunnable]) {
            val fiberRunnable = runnable.asInstanceOf[FiberRunnable]
            val location      = fiberRunnable.location
            if ((location ne null) && (location ne emptyTrace)) {
                if (worker eq null) globalLocations.put(location)
                else worker.submittedLocations.put(location)

                blockingLocations.contains(location)
            } else false
        } else false
    
    private def maybeUnparkWorker(currentState: Int): Unit = {
        val currentSearching = currentState & 0xffff
        val currentActive    = (currentState & 0xffff0000) >> 16

        if (currentActive != poolSize && currentSearching == 0) {
            val worker = idle.poll()
            if (worker ne null) {
                state.getAndAdd(0x10001)
                worker.active = true
                LockSupport.unpark(worker)
            }
        }
    }

    private[this] def makeWorker(): NioScheduler.Worker =
        new NioScheduler.Worker {
            self =>
            override val submittedLocations: NioScheduler.Locations = makeLocations()

            final override def run(): Unit = {
                val globalQueue          = parent.globalQueue
                val workers              = parent.workers
                val state                = parent.state
                val cache                = parent.cache
                val idle                 = parent.idle
                val poolSize             = NioScheduler.poolSize
                val workerTracker        = parent.workersActiveTracker

                var currentBlocking = false
                var currentOpCount  = 0L
                val random          = ThreadLocalRandom.current
                var runnable        = null.asInstanceOf[Runnable]
                var searching       = false

                var currentHardLoadingOpCount = 0L
                
                while (!isInterrupted) {
                    currentBlocking = blocking
                    val currentNextRunnable = nextRunnable
                    if (currentBlocking) ()
                    else if (currentNextRunnable ne null) {
                        runnable = currentNextRunnable
                        nextRunnable = null
                    } else {
                        if (currentHardLoadingOpCount > 127) {
                            workerTracker.touch(self)
                            currentHardLoadingOpCount = 0L
                        }

                        if ((currentOpCount & 63) == 0) {
                            runnable = globalQueue.poll(random)
                            if (runnable eq null) {
                                runnable = localQueue.poll(null)
                            }
                        } else {
                            runnable = localQueue.poll(null)
                            if (runnable eq null) {
                                runnable = globalQueue.poll(random)
                            }
                        }

                        if (runnable eq null) {
                            if (!searching) {
                                val currentState  = state.get
                                val currentActive = currentState & 0xffff

                                if (2 * currentActive < poolSize) {
                                    state.getAndIncrement()
                                    searching = true
                                }
                            }

                            if (searching) {
                                val targetWorker = workerTracker.getBusyWorker()
                                if ((targetWorker ne null) && (targetWorker ne self)) {
                                    val size = targetWorker.localQueue.size()
                                    if (size > 0) {
                                        val runnables = targetWorker.localQueue.pollUpTo(size - size / 2)
                                        val nRunnables = runnables.size
                                        if (nRunnables > 0) {
                                            val iter = runnables.iterator
                                            runnable = iter.next()

                                            if (nRunnables > 1) {
                                                localQueue.offerAll(iter, nRunnables - 1)
                                            }

                                            currentBlocking = blocking

                                            if (currentBlocking) {
                                                val runnables = localQueue.pollUpTo(256)
                                                if (!runnables.isEmpty) {
                                                    globalQueue.offerAll(runnables, random)
                                                }
                                            }
                                        }
                                    }
                                }

                                if (runnable eq null) {
                                    runnable = globalQueue.poll(random)
                                }
                            }
                        }
                    }

                    if (runnable eq null) {
                        val currentState =
                            if (currentBlocking && searching) state.decrementAndGet()
                            else if (currentBlocking) state.get
                            else if (searching) state.addAndGet(0xfffeffff)
                            else state.addAndGet(0xffff0000)
                        
                        val currentSearching = currentState & 0xffff
                        active = false

                        if (currentBlocking) {
                            cache.offer(self)
                        } else {
                            idle.offer(self)
                        }

                        if (currentSearching == 0 && searching) {
                            var i      = 0
                            var notify = false
                            while (i != poolSize && !notify) {
                                val worker = workers(i)
                                notify = !worker.localQueue.isEmpty()
                                i += 1
                            }
                            if (!notify) {
                                notify = !globalQueue.isEmpty()
                            }
                            if (notify) {
                                val currentState = state.get
                                maybeUnparkWorker(currentState)
                            }
                        }

                        while (!active && !isInterrupted) {
                            LockSupport.park()
                        }

                        searching = true
                    } else {
                        if (searching) {
                            searching = false
                            val currentState = state.decrementAndGet()
                            maybeUnparkWorker(currentState)
                        }
                        currentRunnable = runnable
                        runnable.run()
                        
                        runnable = null
                        currentRunnable = runnable
                        currentOpCount += 1
                        opCount = currentOpCount

                        val currentLocalQueueSize = localQueue.size()
                        if (currentLocalQueueSize > 224) {
                            currentHardLoadingOpCount += 3
                        } else if (currentLocalQueueSize > 192) {
                            currentHardLoadingOpCount += 2
                        } else if (currentLocalQueueSize > 128) {
                            currentHardLoadingOpCount += 1
                        } else if (currentLocalQueueSize < 96) {
                            currentHardLoadingOpCount = currentHardLoadingOpCount / 2
                        } else if (currentLocalQueueSize < 64) {
                            currentHardLoadingOpCount = currentHardLoadingOpCount / 3
                        } else {
                            currentHardLoadingOpCount = 0L
                        }

                        hardLoadingOpCount = currentHardLoadingOpCount
                    }
                    
                }

            }

            final def markAsBlocking(): Unit = synchronized {
                if (blocking) ()
                else {
                    val workerTracker = parent.workersActiveTracker
                    val idx           = workers.indexOf(self)

                    blocking = true

                    if (idx >= 0) {
                        val runnables = self.localQueue.pollUpTo(256)
                        if (nextRunnable ne null) {
                            globalQueue.offer(nextRunnable)
                            nextRunnable = null
                        }
                        globalQueue.offerAll(runnables)

                        val worker = cache.poll()
                        if (worker eq null) {
                            val worker = makeWorker()
                            worker.setName(idx)
                            worker.setDaemon(true)
                            workers(idx) = worker
                            workerTracker.replaceWorker(self, worker)
                            worker.start()
                        } else {
                            state.getAndIncrement()
                            worker.setName(idx)
                            workers(idx) = worker
                            workerTracker.replaceWorker(self, worker)
                            worker.blocking = false
                            worker.active = true
                            LockSupport.unpark(worker)
                        }
                    }
                }
            }
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
                                val currentWorkerQueueSize = currentWorker.localQueue.size()
                                if (currentWorkerQueueSize < 32) {
                                    val busyWorker = workersActiveTracker.getBusyWorker()
                                    if ((busyWorker ne null) && (busyWorker ne currentWorker) && (busyWorker.localQueue.size() > 224)) {
                                        val runnables = busyWorker.localQueue.pollUpTo(96)
                                        val nRunnables = runnables.size
                                        if (nRunnables > 0) {
                                            val iter = runnables.iterator

                                            if ((currentWorker.blocking == false) && (currentWorker.active == true) && (currentWorker.localQueue.size() < 48)) {
                                                currentWorker.localQueue.offerAll(iter, nRunnables)
                                            } else {
                                                globalQueue.offerAll(runnables)
                                            }
                                            
                                        }
                                    }
                                }
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


    private[this] def submitBlocking(runnable: Runnable)(implicit unsafe: Unsafe): Boolean =
        Blocking.blockingExecutor.submit(runnable)
    
    
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
                var size = 0
                var i    = 0
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

    def submit(runnable: Runnable)(implicit unsafe: Unsafe): Boolean = {
        val worker = workerOrNull()
        if (isBlocking(worker, runnable)) {
            submitBlocking(runnable)
        } else {
            if ((worker eq null) || worker.blocking) {
                globalQueue.offer(runnable)
            } else if (!worker.localQueue.offer(runnable)) {
                handleFullWorkerQueue(worker, runnable)
            } else ()
            
            val currentState = state.get
            maybeUnparkWorker(currentState)
            true
        }
    }

    override def submitAndYield(runnable: Runnable)(implicit unsafe: Unsafe): Boolean = {
        val worker = workerOrNull()
        if (isBlocking(worker, runnable)) {
            submitBlocking(runnable)
        } else {
            var notify = true

            if ((worker eq null) || worker.blocking) {
                globalQueue.offer(runnable)
            } else if ((worker.nextRunnable eq null) && worker.localQueue.isEmpty()) {
                val fromGlobal = globalQueue.poll()

                if (fromGlobal eq null) {
                    worker.nextRunnable = runnable
                    notify = false
                } else {
                    worker.nextRunnable = fromGlobal
                    worker.localQueue.offer(runnable)
                }
            } else if (!worker.localQueue.offer(runnable)) {
                handleFullWorkerQueue(worker, runnable)
            }

            if (notify) {
                val currentState = state.get
                maybeUnparkWorker(currentState)
            }

            true
        }
    }

    private def handleFullWorkerQueue(worker: NioScheduler.Worker, runnable: Runnable): Unit = {
        val rnd    = ThreadLocalRandom.current
        val polled = worker.localQueue.pollUpTo(128)
        globalQueue.offerAll(polled, rnd)

        val accepted = worker.localQueue.offer(runnable)
        if (!accepted) {
            globalQueue.offer(runnable, rnd)
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

        @volatile
        var active: Boolean = true

        @volatile
        var blocking: Boolean = false

        @volatile
        var currentRunnable: Runnable = null

        val localQueue: RingBufferPow2[Runnable] = RingBufferPow2[Runnable](256)

        var nextRunnable: Runnable = null

        @volatile
        var opCount: Long = 0L

        @volatile
        var hardLoadingOpCount: Long = 0L

        def markAsBlocking(): Unit

        final def setName(i: Int): Unit =
            setName(s"NioScheduler-Worker-$i")

        override def blockOn[T](thunk: => T)(implicit permission: CanAwait): T = {
            markAsBlocking()
            thunk
        }

    }

    private final class WorkerActivityTracker(maxSize: Int) {
        private class Node(var worker: NioScheduler.Worker) {
            var prev: Node = _
            var next: Node = _
        }

        private val nodeMap = new java.util.concurrent.ConcurrentHashMap[NioScheduler.Worker, Node]()
        private val dummyHead = new Node(null)
        private val dummyTail = new Node(null)
        
        dummyHead.next = dummyTail
        dummyTail.prev = dummyHead

        def touch(worker: NioScheduler.Worker): Unit = synchronized {
            var node = nodeMap.get(worker)
            if (node != null) {
                removeNode(node)
            } else {
                node = new Node(worker)
                nodeMap.put(worker, node)
            }
            addToHead(node)

            if (nodeMap.size() > maxSize) {
                val oldest = dummyHead.next
                if (oldest != dummyTail) {
                    nodeMap.remove(oldest.worker)
                    removeNode(oldest)
                }
            }
        }

        def scale(worker: NioScheduler.Worker): Unit = synchronized {
            var node = nodeMap.get(worker)
            if (node != null) {
                removeNode(node)
            } else {
                node = new Node(worker)
                nodeMap.put(worker, node)
            }
            addToTail(node)

            if (nodeMap.size() > maxSize) {
                val oldest = dummyHead.next
                if (oldest != dummyTail) {
                    nodeMap.remove(oldest.worker)
                    removeNode(oldest)
                }
            }
        }

        def getBusyWorker(): NioScheduler.Worker = synchronized {
            if (dummyHead.next == dummyTail) null
            else {
                var busyWorker: NioScheduler.Worker = dummyHead.next.worker
                var p          = dummyHead.next
                var i          = 0
                while ((i < poolSize) && (p ne null) && (p ne dummyTail) && ((p.worker.blocking == true) || (p.worker.active == false))) {
                    i += 1
                    p = p.next
                    if ((p ne null) && (p ne dummyTail)) {
                        busyWorker = p.worker
                    }
                }

                if (busyWorker ne null) {
                    scale(busyWorker)
                }

                busyWorker
            }
        }

        def replaceWorker(workerA: NioScheduler.Worker, workerB: NioScheduler.Worker): Unit = synchronized {
            val node = nodeMap.get(workerA)
            node.worker = workerB
            nodeMap.put(workerB, node)
            nodeMap.remove(workerA)
        }

        private def removeNode(node: Node): Unit = {
            node.prev.next = node.next
            node.next.prev = node.prev
        }

        private def addToTail(node: Node): Unit = {
            node.prev = dummyTail.prev
            node.next = dummyTail
            dummyTail.prev.next = node
            dummyTail.prev = node
        }

        private def addToHead(node: Node): Unit = {
            node.next = dummyHead.next
            node.prev = dummyHead
            dummyHead.next.prev = node
            dummyHead.next = node
        }
    }
}