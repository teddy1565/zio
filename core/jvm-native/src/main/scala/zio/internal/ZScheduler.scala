/*
 * Copyright 2021-2024 John A. De Goes and the ZIO Contributors
 * ... (版權聲明略) ...
 */

package zio.internal

import zio._
import zio.stacktracer.TracingImplicits.disableAutoTrace

import java.util.concurrent.atomic.{AtomicInteger, AtomicLong}
import java.util.concurrent.locks.LockSupport
import java.util.concurrent.{ConcurrentLinkedQueue, ThreadLocalRandom}
import scala.collection.mutable
import scala.concurrent.{BlockContext, CanAwait}

/**
 * `ZScheduler` 是一個專為執行 ZIO 應用程式優化的 `Executor`。
 * 靈感來自 Carl Lerche 的 "Making the Tokio Scheduler 10X Faster"。
 * 它使用工作竊取演算法 (Work Stealing) 並具備自動阻塞檢測機制。
 */
private final class ZScheduler(autoBlocking: Boolean) extends Executor { parent =>

  import Trace.{empty => emptyTrace}
  import ZScheduler.{poolSize, workerOrNull}

  // --- 核心資料結構 ---

  // 全域佇列：當 worker 本地佇列滿了，或者外部提交任務時，會放到這裡。
  // 使用分區佇列 (PartitionedLinkedQueue) 來減少多執行緒競爭 (Contention)。
  private[this] val globalQueue     = new PartitionedLinkedQueue[Runnable](poolSize * 4)

  // 快取佇列：存放之前被替換掉（因為阻塞）但現在已經恢復的 Worker，或者暫時閒置的 Worker。
  private[this] val cache           = new ConcurrentLinkedQueue[ZScheduler.Worker]()

  // 閒置佇列：存放目前沒有工作可做，正在休眠 (Parked) 的 Worker。
  private[this] val idle            = new ConcurrentLinkedQueue[ZScheduler.Worker]()

  // 追蹤程式碼位置：用於自動阻塞檢測，記錄哪些程式碼位置經常導致阻塞。
  private[this] val globalLocations = makeLocations()

  // 狀態原子變數：這是一個 packed integer (32位元整數封裝兩個狀態)。
  // 高 16 位元：代表目前 "Active" (活躍且未阻塞) 的 Worker 數量。
  // 低 16 位元：代表目前 "Searching" (正在尋找工作) 的 Worker 數量。
  // 初始值：活躍數 = poolSize (左移16位)，搜尋數 = 0。
  private[this] val state           = new AtomicInteger(poolSize << 16)

  // Worker 陣列：存放所有核心 Worker 執行緒的參照。
  private[this] val workers         = Array.ofDim[ZScheduler.Worker](poolSize)

  // 阻塞位置集合：紀錄被判定為「會阻塞」的 Trace 位置，之後遇到這些位置的任務會直接丟去 Blocking Pool。
  @volatile private[this] var blockingLocations: Set[Trace] = Set.empty

  // --- 初始化區塊 ---

  // 初始化所有 Worker
  (0 until poolSize).foreach { workerId =>
    val worker = makeWorker()
    worker.setName(workerId) // 設定執行緒名稱
    worker.setDaemon(true)   // 設定為守護執行緒 (Daemon)，主程式結束它就會結束
    workers(workerId) = worker
  }
  // 啟動所有 Worker 執行緒
  workers.foreach(_.start())

  // 如果開啟了自動阻塞檢測 (Auto-blocking)，則啟動 Supervisor 執行緒
  if (autoBlocking) {
    val supervisor = makeSupervisor()
    supervisor.setName("ZScheduler-Supervisor")
    supervisor.setDaemon(true)
    supervisor.start()
  }

  // 判斷當前執行緒是否為 ZScheduler 的 Worker
  override private[zio] def isCurrentThreadInExecutor: Boolean =
    Thread.currentThread().isInstanceOf[ZScheduler.Worker]

  // --- Metrics (指標) 相關 ---
  // 用於監控 Executor 的健康狀態
  def metrics(implicit unsafe: Unsafe): Option[ExecutionMetrics] = {
    val metrics = new ExecutionMetrics {
      def capacity: Int = Int.MaxValue // 容量視為無限
      def concurrency: Int = poolSize  // 並發數等於核心數
      
      // 計算所有 Worker 已處理的任務總數
      def dequeuedCount: Long = {
        var dequeued = 0L
        var i        = 0
        while (i != poolSize) {
          val worker = workers(i)
          dequeued += worker.opCount // opCount 是每個 worker 的計數器
          i += 1
        }
        dequeued
      }

      // 計算目前排隊中的任務總數 (本地 + 全域 + 下一個待執行)
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

      // 計算目前系統中積壓的任務數
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

      // 從 state 解析出目前活躍的 worker 數量
      def workersCount: Int = {
        val currentState = state.get
        (currentState & 0xffff0000) >> 16 // 取高 16 位
      }
    }
    Some(metrics)
  }

  // --- 工作竊取邏輯 (Steal Work) ---
  // 允許目前的 Worker 從其他地方偷工作來做 (主要用於幫助處理任務)
  override def stealWork(depth: Int): Boolean = {
    val worker = workerOrNull()
    if (worker ne null) { // 只有 Worker 執行緒能執行此優化
      var runnable = null.asInstanceOf[Runnable]
      
      // 1. 優先檢查自己的 nextRunnable 插槽 (最快路徑)
      if (worker.nextRunnable ne null) {
        runnable = worker.nextRunnable
        worker.nextRunnable = null
      } else {
        // 2. 檢查自己的本地佇列
        runnable = worker.localQueue.poll(null)
        if (runnable eq null) {
          // 3. 最後檢查全域佇列
          runnable = globalQueue.poll()
        }
      }

      if (runnable ne null) {
        // 如果是 FiberRunnable，可以遞迴執行 (傳入 depth)
        if (runnable.isInstanceOf[FiberRunnable]) {
          val fiberRunnable = runnable.asInstanceOf[FiberRunnable]
          worker.currentRunnable = fiberRunnable
          fiberRunnable.run(depth)
        } else {
          runnable.run()
        }
        true
      } else {
        worker.nextRunnable = runnable // 沒偷到，重置
        false
      }
    } else {
      false
    }
  }

  // --- 提交任務 (Submit) ---
  // 外部執行緒或內部 Worker 提交新任務
  def submit(runnable: Runnable)(implicit unsafe: Unsafe): Boolean = {
    val worker = workerOrNull()
    
    // 檢查是否為已知的阻塞任務，若是則直接丟給 Blocking Executor
    if (isBlocking(worker, runnable)) {
      submitBlocking(runnable)
    } else {
      // 如果不是 Worker 呼叫，或是該 Worker 已經處於阻塞狀態
      if ((worker eq null) || worker.blocking) {
        globalQueue.offer(runnable) // 丟到全域佇列
      } 
      // 嘗試放入 Worker 的本地佇列，如果滿了才處理溢出
      else if (!worker.localQueue.offer(runnable)) {
        handleFullWorkerQueue(worker, runnable)
      } else ()
      
      // 喚醒可能在睡覺的 Worker 來處理新任務
      val currentState = state.get
      maybeUnparkWorker(currentState)
      true
    }
  }
  
  // --- 提交並讓出 (Submit and Yield) ---
  // 當 Fiber 主動暫停 (Yield) 時呼叫，目的是為了公平性讓出 CPU
  override def submitAndYield(runnable: Runnable)(implicit unsafe: Unsafe): Boolean = {
    val worker = workerOrNull()
    if (isBlocking(worker, runnable)) {
      submitBlocking(runnable)
    } else {
      var notify = true
      
      // 情況 1: 非 Worker 或 Worker 已阻塞 -> 丟全域
      if ((worker eq null) || worker.blocking) {
        globalQueue.offer(runnable)
      }
      // 情況 2: 嘗試留在當前執行緒 (為了 CPU Cache Locality 優化)
      // 如果 nextRunnable 是空的且本地佇列也是空的
      else if ((worker.nextRunnable eq null) && worker.localQueue.isEmpty()) {
        // 理想情況下我們該做一次完整的工作竊取，但太貴了。這裡只檢查全域佇列。
        val fromGlobal = globalQueue.poll()
        
        // Happy path: 全域沒東西，我們可以放心地把自己排在下一個執行 (最快恢復)
        if (fromGlobal eq null) {
          worker.nextRunnable = runnable
          notify = false // 不需要喚醒其他人，因為我們自己馬上就會接手
        } else {
          // 如果全域有東西，為了公平，優先執行全域的任務，把原本要 Yield 的任務放回佇列尾端
          worker.nextRunnable = fromGlobal
          worker.localQueue.offer(runnable)
        }
      }
      // 情況 3: 必須 Yield，且上述優化不適用，嘗試放入本地佇列
      else if (!worker.localQueue.offer(runnable)) {
        handleFullWorkerQueue(worker, runnable)
      }

      if (notify) {
        val currentState = state.get
        maybeUnparkWorker(currentState)
      }
      true
    }
  }

  // 處理 Worker 本地佇列已滿的情況
  private def handleFullWorkerQueue(worker: ZScheduler.Worker, runnable: Runnable): Unit = {
    val rnd    = ThreadLocalRandom.current
    // 從本地佇列取出一半 (128個) 的任務
    val polled = worker.localQueue.pollUpTo(128)
    // 丟到全域佇列，讓其他 Worker 可以幫忙做
    globalQueue.offerAll(polled, rnd)
    // 再次嘗試把新任務放入本地佇列
    val accepted = worker.localQueue.offer(runnable)
    if (!accepted) {
      // 預防萬一：如果還是滿的 (極少見)，直接丟全域
      globalQueue.offer(runnable, rnd)
    }
  }

  // 判斷任務是否應該被視為「阻塞操作」
  private[this] def isBlocking(worker: ZScheduler.Worker, runnable: Runnable): Boolean =
    if (autoBlocking && runnable.isInstanceOf[FiberRunnable]) {
      val fiberRunnable = runnable.asInstanceOf[FiberRunnable]
      val location      = fiberRunnable.location // 取得程式碼 Trace 位置
      if ((location ne null) && (location ne emptyTrace)) {
        // 記錄這個位置出現過
        if (worker eq null) globalLocations.put(location)
        else worker.submittedLocations.put(location)
        // 檢查這個位置是否在黑名單中
        blockingLocations.contains(location)
      } else false
    } else false

  // 根據設定建立 Locations 追蹤器
  private[this] def makeLocations(): ZScheduler.Locations =
    if (autoBlocking) new ZScheduler.Locations.Enabled
    else ZScheduler.Locations.Disabled

  // --- Supervisor (監工) ---
  // 負責監控 Worker 是否卡死 (阻塞)
  private[this] def makeSupervisor(): ZScheduler.Supervisor =
    new ZScheduler.Supervisor {

      // 計算某個程式碼位置被提交的總次數
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
        val previousOpCounts    = Array.fill(poolSize)(-1L) // 紀錄上一次檢查時每個 Worker 的操作數
        
        while (!isInterrupted) {
          var workerId = 0
          while (workerId < poolSize) {
            val currentWorker = workers(workerId)
            if (currentWorker.active) {
              val currentOpCount  = currentWorker.opCount
              val previousOpCount = previousOpCounts(workerId)
              
              // 關鍵判斷：如果操作數 (opCount) 與上次檢查時相同，代表 Worker 卡住了
              if (currentOpCount == previousOpCount) {
                val currentRunnable = currentWorker.currentRunnable
                
                // --- 阻塞歸因邏輯 ---
                if (currentRunnable.isInstanceOf[FiberRunnable]) {
                  val fiberRunnable = currentRunnable.asInstanceOf[FiberRunnable]
                  val location      = fiberRunnable.location
                  if (location ne emptyTrace) {
                    val identifiedCount = identifiedLocations.put(location)
                    val submittedCount  = countSubmittedAt(location)
                    // 啟發式演算法：如果某個位置提交超過 64 次，且其中一半以上導致了阻塞
                    if (submittedCount > 64 && identifiedCount >= submittedCount / 2) {
                      blockingLocations += location // 加入黑名單
                    }
                  }
                }
                // 重置計數器並將該 Worker 標記為阻塞 (這會觸發生成新 Worker)
                previousOpCounts(workerId) = -1L
                currentWorker.markAsBlocking()
              } else {
                // Worker 有在動，更新計數器
                previousOpCounts(workerId) = currentOpCount
              }
            } else {
              previousOpCounts(workerId) = -1L
            }
            workerId += 1
          }
          
          // 監工每 100ms 檢查一次
          val deadline = java.lang.System.currentTimeMillis() + 100
          var loop     = true
          while (loop) {
            LockSupport.parkUntil(deadline)
            loop = java.lang.System.currentTimeMillis() < deadline
          }
        }
      }
    }

  // --- Worker 實作 ---
  private[this] def makeWorker(): ZScheduler.Worker =
    new ZScheduler.Worker {
      self =>
      override val submittedLocations: ZScheduler.Locations = makeLocations()

      final override def run(): Unit = {
        // 將父物件的變數複製到 Stack 上以加速存取 (避免一直從 Heap 讀取 parent)
        val globalQueue = parent.globalQueue
        val workers     = parent.workers
        val state       = parent.state
        val cache       = parent.cache
        val idle        = parent.idle
        val poolSize    = ZScheduler.poolSize

        var currentBlocking = false
        var currentOpCount  = 0L
        val random          = ThreadLocalRandom.current
        var runnable        = null.asInstanceOf[Runnable]
        var searching       = false // 標記是否處於「搜尋工作模式」

        while (!isInterrupted) {
          currentBlocking = blocking
          val currentNextRunnable = nextRunnable
          
          // 1. 如果已標記為阻塞，不做事 (由 markAsBlocking 處理後續)
          if (currentBlocking) ()
          // 2. 優先執行 nextRunnable (快速通道)
          else if (currentNextRunnable ne null) {
            runnable = currentNextRunnable
            nextRunnable = null
          } else {
            // 3. 一般輪詢邏輯
            // 每 64 次操作檢查一次全域佇列，避免全域任務飢餓 (Starvation)
            if ((currentOpCount & 63) == 0) {
              runnable = globalQueue.poll(random)
              if (runnable eq null) {
                runnable = localQueue.poll(null)
              }
            } else {
              // 一般情況先看本地，沒有再看全域
              runnable = localQueue.poll(null)
              if (runnable eq null) {
                runnable = globalQueue.poll(random)
              }
            }

            // 4. 如果還是沒工作，進入搜尋模式 (Work Stealing)
            if (runnable eq null) {
              if (!searching) {
                val currentState  = state.get
                val currentActive = currentState & 0xffff // 取低 16 位 (活躍數與搜尋數計算方式略有不同，此處簡化理解為檢查活躍比例)
                // 如果目前搜尋中的 worker 不多，則允許進入搜尋模式
                if (2 * currentActive < poolSize) {
                  state.getAndIncrement() // 增加搜尋者計數
                  searching = true
                }
              }
              
              if (searching) {
                // 開始隨機竊取工作
                var i      = 0
                var loop   = true
                val offset = random.nextInt(poolSize) // 隨機起點
                while (i != poolSize && loop) {
                  val index  = (i + offset) % poolSize
                  val worker = workers(index)
                  // 不能偷自己，也不能偷阻塞中的 worker
                  if ((worker ne self) && !worker.blocking) {
                    val size = worker.localQueue.size()
                    if (size > 0) {
                      // 偷走一半的工作
                      val runnables  = worker.localQueue.pollUpTo(size - size / 2)
                      val nRunnables = runnables.size
                      if (nRunnables > 0) {
                        val iter = runnables.iterator
                        runnable = iter.next() // 拿到一個工作
                        // 如果偷到多個，剩下的放回自己的本地佇列
                        if (nRunnables > 1) localQueue.offerAll(iter, nRunnables - 1)
                        
                        // 檢查竊取過程中是否自己變成了阻塞狀態 (極端情況)
                        currentBlocking = blocking
                        if (currentBlocking) {
                          val runnables = localQueue.pollUpTo(256)
                          if (!runnables.isEmpty) {
                            globalQueue.offerAll(runnables, random)
                          }
                        }
                        loop = false // 找到了，結束搜尋
                      }
                    }
                  }
                  i += 1
                }
                // 如果偷了一圈還是沒有，最後再看一次全域
                if (runnable eq null) {
                  runnable = globalQueue.poll(random)
                }
              }
            }
          }

          // 5. 還是沒工作 -> 準備休眠 (Park)
          if (runnable eq null) {
            val currentState =
              if (currentBlocking && searching) state.decrementAndGet() // 減少搜尋計數
              else if (currentBlocking) state.get
              else if (searching) state.addAndGet(0xfffeffff) // 減少搜尋計數並調整狀態
              else state.addAndGet(0xffff0000) // 減少活躍計數 (Active count)

            val currentSearching = currentState & 0xffff
            active = false // 標記為非活躍
            
            // 根據是否阻塞決定去哪個佇列等待
            if (currentBlocking) {
              cache.offer(self)
            } else {
              idle.offer(self)
            }

            // Double check: 在睡覺前最後檢查一次有沒有新工作進來，避免 race condition
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

            // 正式休眠，等待 LockSupport.unpark 喚醒
            while (!active && !isInterrupted) {
              LockSupport.park()
            }
            searching = true // 醒來後預設進入搜尋模式
          } else {
            // 6. 有工作 -> 執行工作
            if (searching) {
              searching = false
              val currentState = state.decrementAndGet() // 退出搜尋狀態
              maybeUnparkWorker(currentState) // 可能需要喚醒其他人幫忙
            }
            currentRunnable = runnable
            runnable.run() // **執行任務**
            
            // 清理狀態
            runnable = null
            currentRunnable = runnable
            currentOpCount += 1
            opCount = currentOpCount // 更新操作計數 (給 Supervisor 看)
          }
        }
      }

      // --- 標記為阻塞 (Mark As Blocking) ---
      // 當 Worker 偵測到自己被阻塞 (Supervisor 觸發或主動呼叫) 時執行
      // NOTE: 使用 synchronized 是為了防止 Supervisor 和外部同時呼叫造成衝突
      final def markAsBlocking(): Unit = synchronized {
        if (blocking) ()
        else {
          blocking = true // 設定 flag
          val idx = workers.indexOf(self)
          if (idx >= 0) {
            // 1. 把身上的工作全部丟出去 (給全域佇列)
            val runnables = self.localQueue.pollUpTo(256)
            if (nextRunnable ne null) {
              globalQueue.offer(nextRunnable)
              nextRunnable = null
            }
            globalQueue.offerAll(runnables)
            
            // 2. 找一個替補 Worker
            val worker = cache.poll() // 先看快取有沒有舊的
            if (worker eq null) {
              // 沒有就造一個新的 Worker 頂替自己的位置
              val worker = makeWorker()
              worker.setName(idx)
              worker.setDaemon(true)
              workers(idx) = worker // 替換掉陣列中的參照
              worker.start()
            } else {
              // 有舊的就喚醒它
              state.getAndIncrement()
              worker.setName(idx)
              workers(idx) = worker
              worker.blocking = false
              worker.active = true
              LockSupport.unpark(worker)
            }
          }
        }
      }
    }

  // --- 喚醒 Worker (Unpark) ---
  // 當有新任務加入時，檢查是否需要喚醒閒置的 Worker
  private def maybeUnparkWorker(currentState: Int): Unit = {
    val currentSearching = currentState & 0xffff
    val currentActive    = (currentState & 0xffff0000) >> 16
    // 如果活躍 Worker 沒滿，且沒有人在搜尋工作，那就喚醒一個
    if (currentActive != poolSize && currentSearching == 0) {
      val worker = idle.poll()
      if (worker ne null) {
        state.getAndAdd(0x10001) // 增加活躍數與搜尋數
        worker.active = true
        LockSupport.unpark(worker) // 叫醒它
      }
    }
  }

  // 將任務提交給專用的 Blocking Executor
  private[this] def submitBlocking(runnable: Runnable)(implicit unsafe: Unsafe): Boolean =
    Blocking.blockingExecutor.submit(runnable)
}

// --- 伴生物件 (Companion Object) ---
private object ZScheduler {
  // 預設執行緒池大小 = CPU 核心數
  private val poolSize = java.lang.Runtime.getRuntime.availableProcessors

  // 提供給外部呼叫：強制標記當前 Worker 為阻塞
  def markCurrentWorkerAsBlocking(): Unit = {
    val worker = workerOrNull()
    if (worker ne null) {
      worker.markAsBlocking()
    } else {
      ()
    }
  }

  // 取得當前執行緒的 Worker 物件 (如果有的話)
  private def workerOrNull(): ZScheduler.Worker =
    Thread.currentThread() match {
      case w: ZScheduler.Worker => w
      case _                    => null
    }

  /**
   * `Locations` 用於追蹤 Fiber 產生的位置，是自動阻塞檢測的核心資料結構。
   */
  private sealed abstract class Locations {
    def get(trace: Trace): Long
    def put(trace: Trace): Long
  }

  private object Locations {
    // 啟用追蹤：使用 HashMap 紀錄次數
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

    // 禁用追蹤：不做任何事
    object Disabled extends Locations {
      def get(trace: Trace): Long = 0L
      def put(trace: Trace): Long = 0L
    }
  }

  // Supervisor 執行緒的抽象定義
  private sealed abstract class Supervisor extends Thread

  // Worker 執行緒的抽象定義，實作了 BlockContext (Scala 的阻塞上下文)
  private sealed abstract class Worker extends Thread with BlockContext {

    val submittedLocations: Locations

    // Worker 是否活躍 (正在跑或準備跑)
    @volatile
    var active: Boolean = true

    // Worker 是否處於阻塞替換狀態
    @volatile
    var blocking: Boolean = false

    // 當前正在跑的任務
    @volatile
    var currentRunnable: Runnable = null

    // 本地佇列：大小為 256 的 RingBuffer (最快存取)
    val localQueue: RingBufferPow2[Runnable] =
      RingBufferPow2[Runnable](256)

    // 下一個立即執行的任務 (優化用，比佇列還快)
    var nextRunnable: Runnable = null

    // 已執行任務計數 (用於心跳檢測)
    @volatile
    var opCount: Long = 0L

    def markAsBlocking(): Unit

    // 設定易讀的執行緒名稱
    final def setName(i: Int): Unit =
      setName(s"ZScheduler-Worker-$i")

    // 實作 scala.concurrent.BlockContext
    // 當在 Scala Future 中呼叫 blocking { ... } 時會觸發此方法
    override def blockOn[T](thunk: => T)(implicit permission: CanAwait): T = {
      markAsBlocking() // 既然你要阻塞，我就把你標記為阻塞並生一個新的 Worker
      thunk
    }
  }
}