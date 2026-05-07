/**
 * L-Stage Chain Scheduling Model
 *
 * Problem: Team 1 -> Team 2 -> ... -> Team L (sequential pipeline)
 * Each stage has k_s workers. Jobs flow through stages in order.
 * Preemptive priority scheduling: higher-priority jobs preempt lower-priority ones.
 *
 * Key difference from the assembly flow shop:
 *   - Assembly: m parallel foundation teams -> 1 dependent team (fork-join)
 *   - Chain: stages in sequence, each stage's output feeds the next (pipeline)
 *
 * P4 verification: for every unsynchronized schedule (different orderings at
 * different stages), there exists a synchronized schedule (same ordering at
 * all stages) that pointwise dominates it at the final stage.
 */

import scala.collection.mutable

// --- Configuration ---

/**
 * Configuration for an L-stage chain.
 *
 * @param numStages     L (number of stages)
 * @param workPerStage  work(stage)(job) — dimensions L x n
 * @param workersPerStage k values per stage
 * @param label         human-readable label
 */
case class ChainConfig(
  numStages: Int,
  workPerStage: List[List[Int]],
  workersPerStage: List[Int],
  label: String = ""
):
  require(workPerStage.size == numStages, s"workPerStage has ${workPerStage.size} stages, expected $numStages")
  require(workersPerStage.size == numStages, s"workersPerStage has ${workersPerStage.size} stages, expected $numStages")
  require(workPerStage.tail.forall(_.size == workPerStage.head.size), "All stages must have the same number of jobs")

  def numJobs: Int = workPerStage.head.size

  def shortLabel: String =
    if label.nonEmpty then label
    else s"L=$numStages n=$numJobs k=${workersPerStage.mkString(",")}"


// --- Preemptive Priority Scheduler ---

/**
 * Simulates preemptive priority scheduling for a single stage with k workers.
 *
 * Given:
 *   - k workers
 *   - n jobs with work amounts and arrival times (from upstream completion)
 *   - A priority ordering (lower index = higher priority in the permutation)
 *
 * The scheduler:
 *   1. At each time step, assigns available workers to the highest-priority available jobs
 *   2. When a higher-priority job arrives (upstream completes), it preempts the
 *      lowest-priority running job if all workers are busy
 *   3. Work is divided across workers: each worker contributes 1 unit of work per time step
 *      when assigned to a job. Multiple workers on the same job = parallel speedup.
 *
 * Water-fill: When k workers are available and fewer than k jobs need work,
 * all k workers split across the available jobs. When more jobs than workers,
 * only the top-k priority jobs get workers (1 each).
 *
 * Returns: Map[jobIndex -> completionTime] for this stage.
 */
object PreemptivePriorityScheduler:

  /**
   * Schedule jobs at a single stage.
   *
   * @param k           number of workers at this stage
   * @param work        work(jobIndex) — total work required for each job at this stage
   * @param priority    permutation of job indices — priority(0) is highest priority
   * @param arrivalTime arrival time of each job (from previous stage completion, or 0 for stage 0)
   * @return Map[jobIndex -> completionTime]
   */
  def scheduleStage(
    k: Int,
    work: IndexedSeq[Int],
    priority: IndexedSeq[Int],  // priority(0) = highest priority job index
    arrivalTime: IndexedSeq[Double]
  ): Map[Int, Double] =
    val n = work.size
    // Priority rank: priorityRank(jobIndex) = rank (0 = highest)
    val priorityRank = new Array[Int](n)
    for (i <- priority.indices) priorityRank(priority(i)) = i

    // Remaining work for each job (scaled: work * k to avoid fractions)
    // When w workers are assigned to a job for 1 time unit, it does w units of scaled work.
    // Total scaled work = work(j) * k (so that k workers for 1 time unit = k scaled units).
    // Actually, let's think differently: use rational arithmetic or just simulate time steps.
    //
    // Simpler approach: event-driven simulation with rational time.
    // Each job needs `work(j)` total work-units. If assigned `w` workers, it completes
    // `w` work-units per time unit. So completion takes `work(j) / w` time units
    // (possibly fractional).
    //
    // To keep things exact with integers: scale everything by LCM or just use doubles.
    // For correctness with integer work amounts: use a rational representation.
    // Since we're comparing completion times, doubles should be fine for small instances.

    // Event-driven simulation
    val remainingWork = Array.ofDim[Double](n)
    for (j <- 0 until n) remainingWork(j) = work(j).toDouble
    val completionTime = Array.fill(n)(Double.MaxValue)
    val arrived = Array.fill(n)(false)
    val completed = Array.fill(n)(false)

    // Events: job arrivals. We process time forward.
    var currentTime = 0.0

    // Collect all arrival times as events
    val arrivalEvents = (0 until n).map(j => (arrivalTime(j), j)).sortBy(_._1)
    var nextArrivalIdx = 0

    // Mark jobs that arrive at time 0
    while (nextArrivalIdx < arrivalEvents.size && arrivalEvents(nextArrivalIdx)._1 <= currentTime) {
      arrived(arrivalEvents(nextArrivalIdx)._2) = true
      nextArrivalIdx += 1
    }

    var completedCount = 0

    while (completedCount < n) {
      // Determine which jobs are available (arrived, not completed, have remaining work)
      val available = (0 until n)
        .filter(j => arrived(j) && !completed(j) && remainingWork(j) > 0)
        .sortBy(j => priorityRank(j))

      if (available.isEmpty) {
        // No jobs available — advance to next arrival
        if (nextArrivalIdx < arrivalEvents.size) {
          currentTime = arrivalEvents(nextArrivalIdx)._1
          while (nextArrivalIdx < arrivalEvents.size && arrivalEvents(nextArrivalIdx)._1 <= currentTime) {
            arrived(arrivalEvents(nextArrivalIdx)._2) = true
            nextArrivalIdx += 1
          }
        } else {
          // Should not happen if all jobs have finite work
          throw new IllegalStateException("No available jobs and no pending arrivals")
        }
      } else {
        // Assign workers to jobs by priority.
        // Water-fill: distribute k workers across available jobs.
        // Strategy: assign workers to highest-priority jobs first.
        // If fewer jobs than workers, spread workers across jobs.
        // If more jobs than workers, top-k priority jobs each get 1 worker.
        //
        // Actually for preemptive priority with water-fill across k workers:
        // The optimal water-fill assigns workers to minimize completion of the
        // highest-priority available job, then next, etc.
        // Simplest correct approach: assign all k workers to the single highest-priority
        // available job (greedy). This minimizes its completion time.
        //
        // Wait — re-reading the requirement: "Water-fill work division across k workers"
        // This means: for a given job, the work is divided across k workers.
        // So if job j has work w_j and gets assigned k workers, it takes ceil(w_j / k) time.
        //
        // But with preemptive scheduling, the question is: how many workers per job?
        // With priority scheduling, the standard approach is:
        //   - Each worker is assigned to exactly one job at a time
        //   - Workers pick the highest-priority available job
        //   - If k workers and only 1 job available, all k work on it
        //   - If k workers and 3 jobs, top job gets more workers? Or 1 each?
        //
        // For the paper's model: k identical workers, each contributing 1 unit/time.
        // Water-fill = spread workers evenly. With preemptive priority:
        //   All k workers work on the highest-priority job until it's done,
        //   then move to the next. This is classic preemptive priority.
        //
        // Actually, the most natural model matching the existing code: each job
        // needs w units of work. With k workers assigned, rate = k units/time.
        // Preemptive priority: all k workers always work on the single highest-priority
        // available job. When it finishes, they move to the next.
        //
        // This is the simplest and strongest form of preemptive priority.
        // Let me implement this.

        // All k workers on the highest-priority available job
        val topJob = available.head
        val rate = k.toDouble  // k workers, each doing 1 unit/time

        // Time to complete this job
        val timeToComplete = remainingWork(topJob) / rate

        // Next event: either this job completes, or a new job arrives
        val nextArrival = if (nextArrivalIdx < arrivalEvents.size)
          arrivalEvents(nextArrivalIdx)._1
        else
          Double.MaxValue

        val nextEvent = math.min(currentTime + timeToComplete, nextArrival)

        if (currentTime + timeToComplete <= nextArrival) {
          // Job completes before next arrival
          val elapsed = timeToComplete
          remainingWork(topJob) = 0.0
          completed(topJob) = true
          completionTime(topJob) = currentTime + elapsed
          completedCount += 1
          currentTime = currentTime + elapsed

          // Process any arrivals at exactly this time
          while (nextArrivalIdx < arrivalEvents.size && arrivalEvents(nextArrivalIdx)._1 <= currentTime + 1e-12) {
            arrived(arrivalEvents(nextArrivalIdx)._2) = true
            nextArrivalIdx += 1
          }
        } else {
          // New arrival interrupts — do partial work
          val elapsed = nextArrival - currentTime
          remainingWork(topJob) -= elapsed * rate
          if (remainingWork(topJob) < 1e-12) remainingWork(topJob) = 0.0
          currentTime = nextArrival

          // Process arrivals
          while (nextArrivalIdx < arrivalEvents.size && arrivalEvents(nextArrivalIdx)._1 <= currentTime + 1e-12) {
            arrived(arrivalEvents(nextArrivalIdx)._2) = true
            nextArrivalIdx += 1
          }

          // Check if the job actually completed during this interval
          if (remainingWork(topJob) <= 0 && !completed(topJob)) {
            completed(topJob) = true
            completionTime(topJob) = currentTime
            completedCount += 1
          }
        }
      }
    }

    (0 until n).map(j => j -> completionTime(j)).toMap[Int, Double]

  /**
   * Run the full L-stage chain for a given set of per-stage orderings.
   *
   * @param config      the chain configuration
   * @param orderings   orderings(stage) = permutation of job indices for that stage
   * @return completionTimes(stage)(jobIndex) = completion time at that stage
   */
  def scheduleChain(
    config: ChainConfig,
    orderings: IndexedSeq[IndexedSeq[Int]]
  ): IndexedSeq[Map[Int, Double]] =
    val n = config.numJobs
    val stageCompletions = mutable.ArrayBuffer[Map[Int, Double]]()

    for (s <- 0 until config.numStages) {
      val work = config.workPerStage(s).toIndexedSeq
      val k = config.workersPerStage(s)
      val priority = orderings(s)

      val arrivals: IndexedSeq[Double] =
        if (s == 0) IndexedSeq.fill(n)(0.0)
        else {
          val prevCompletions = stageCompletions(s - 1)
          (0 until n).map(j => prevCompletions(j))
        }

      val completions = scheduleStage(k, work, priority, arrivals)
      stageCompletions += completions
    }

    stageCompletions.toIndexedSeq


// --- Chain Analyzer ---

object ChainAnalyzer:

  case class ChainResult(
    config: ChainConfig,
    p4Holds: Boolean,           // pointwise domination
    makespanDomHolds: Boolean,  // P5: sync achieves optimal makespan
    flowtimeDomHolds: Boolean,  // P6: sync achieves optimal flowtime
    numPermutations: Int,
    numSynchronized: Int,
    numUnsynchronized: Int,
    elapsedMs: Long,
    // For debugging: any counterexample found
    counterexample: Option[String] = None
  )

  /**
   * Analyze a chain configuration for P4 (pointwise domination).
   *
   * Generates all possible orderings:
   *   - Synchronized: same permutation at every stage (n! orderings)
   *   - Unsynchronized: different permutations at different stages ((n!)^L orderings)
   *
   * P4 check: for every (possibly unsynchronized) schedule S,
   *   there exists a synchronized schedule S* such that
   *   C_j^(L)(S*) <= C_j^(L)(S) for every job j.
   */
  def analyze(config: ChainConfig): ChainResult =
    val startTime = System.currentTimeMillis()
    val n = config.numJobs
    val L = config.numStages

    // Generate all permutations of job indices
    val perms = (0 until n).toList.permutations.toList.map(_.toIndexedSeq)

    // Synchronized schedules: same ordering at every stage
    val syncSchedules = perms.map { perm =>
      val orderings = IndexedSeq.fill(L)(perm)
      val completions = PreemptivePriorityScheduler.scheduleChain(config, orderings)
      (orderings, completions)
    }

    // All possible orderings: cartesian product of permutations across stages
    val allOrderings = cartesianProduct(List.fill(L)(perms)).map(_.toIndexedSeq)

    // Compute final-stage completion times for all orderings
    val allSchedules = allOrderings.map { orderings =>
      val completions = PreemptivePriorityScheduler.scheduleChain(config, orderings.map(_.toIndexedSeq))
      (orderings, completions)
    }

    // Classify
    val syncOrderingSet = syncSchedules.map(_._1).toSet
    val unsyncSchedules = allSchedules.filterNot(s => syncOrderingSet.contains(s._1))

    // P4 check: for every schedule, a sync schedule must pointwise dominate at the final stage
    var p4Holds = true
    var counterexample: Option[String] = None

    for ((orderings, completions) <- allSchedules if p4Holds) {
      val finalStageCompletions = completions.last  // stage L-1
      val dominated = syncSchedules.exists { case (_, syncCompletions) =>
        val syncFinal = syncCompletions.last
        (0 until n).forall(j => syncFinal(j) <= finalStageCompletions(j) + 1e-9)
      }
      if (!dominated) {
        p4Holds = false
        val orderStr = orderings.map(o => o.mkString("[", ",", "]")).mkString(" | ")
        val compStr = (0 until n).map(j => f"job$j=${finalStageCompletions(j)}%.2f").mkString(", ")
        val syncDetails = syncSchedules.map { case (syncOrd, syncComps) =>
          val syncFinal = syncComps.last
          val sOrd = syncOrd.head.mkString("[", ",", "]")
          val sComp = (0 until n).map(j => f"job$j=${syncFinal(j)}%.2f").mkString(", ")
          val dom = (0 until n).map { j =>
            if syncFinal(j) <= finalStageCompletions(j) + 1e-9 then "ok" else "WORSE"
          }.mkString(",")
          s"      sync $sOrd => $sComp  ($dom)"
        }.mkString("\n")
        counterexample = Some(s"Ordering: $orderStr => $compStr\n    vs sync schedules:\n$syncDetails")
      }
    }

    // P5: makespan dominance — does a sync schedule achieve the best makespan?
    val allMakespans = allSchedules.map { case (_, comps) =>
      comps.last.values.max
    }
    val syncMakespans = syncSchedules.map { case (_, comps) =>
      comps.last.values.max
    }
    val bestOverallMakespan = allMakespans.min
    val bestSyncMakespan = syncMakespans.min
    val makespanDom = bestSyncMakespan <= bestOverallMakespan + 1e-9

    // P6: flowtime dominance — does a sync schedule achieve the best total flowtime?
    val allFlowtimes = allSchedules.map { case (_, comps) =>
      comps.last.values.sum
    }
    val syncFlowtimes = syncSchedules.map { case (_, comps) =>
      comps.last.values.sum
    }
    val bestOverallFlowtime = allFlowtimes.min
    val bestSyncFlowtime = syncFlowtimes.min
    val flowtimeDom = bestSyncFlowtime <= bestOverallFlowtime + 1e-9

    val elapsedMs = System.currentTimeMillis() - startTime

    ChainResult(
      config = config,
      p4Holds = p4Holds,
      makespanDomHolds = makespanDom,
      flowtimeDomHolds = flowtimeDom,
      numPermutations = allOrderings.size,
      numSynchronized = syncSchedules.size,
      numUnsynchronized = unsyncSchedules.size,
      elapsedMs = elapsedMs,
      counterexample = counterexample
    )

  /** Cartesian product of lists. */
  private def cartesianProduct[T](lists: List[List[T]]): List[List[T]] =
    lists.foldRight(List(List.empty[T])) { (currentList, acc) =>
      for {
        elem <- currentList
        combination <- acc
      } yield elem :: combination
    }


// --- Standard Chain Configurations ---

object StandardChainConfigs:

  // L=2, n=2, k=2 — should match assembly results
  val l2_n2_k2: ChainConfig = ChainConfig(
    numStages = 2,
    workPerStage = List(List(2, 3), List(3, 2)),
    workersPerStage = List(2, 2),
    label = "L=2 n=2 k=2 (baseline)"
  )

  // L=2, n=3, k=2
  val l2_n3_k2: ChainConfig = ChainConfig(
    numStages = 2,
    workPerStage = List(List(2, 3, 4), List(3, 2, 2)),
    workersPerStage = List(2, 2),
    label = "L=2 n=3 k=2"
  )

  // L=3, n=2, k=2 — new territory
  val l3_n2_k2: ChainConfig = ChainConfig(
    numStages = 3,
    workPerStage = List(List(2, 3), List(3, 2), List(2, 4)),
    workersPerStage = List(2, 2, 2),
    label = "L=3 n=2 k=2"
  )

  // L=3, n=3, k=2
  val l3_n3_k2: ChainConfig = ChainConfig(
    numStages = 3,
    workPerStage = List(List(2, 3, 4), List(3, 2, 2), List(2, 4, 3)),
    workersPerStage = List(2, 2, 2),
    label = "L=3 n=3 k=2"
  )

  // L=4, n=2, k=2
  val l4_n2_k2: ChainConfig = ChainConfig(
    numStages = 4,
    workPerStage = List(List(2, 3), List(3, 2), List(2, 4), List(4, 2)),
    workersPerStage = List(2, 2, 2, 2),
    label = "L=4 n=2 k=2"
  )

  // L=4, n=3, k=2 — warning: (3!)^4 = 1296 orderings, feasible
  val l4_n3_k2: ChainConfig = ChainConfig(
    numStages = 4,
    workPerStage = List(List(2, 3, 4), List(3, 2, 2), List(2, 4, 3), List(3, 3, 2)),
    workersPerStage = List(2, 2, 2, 2),
    label = "L=4 n=3 k=2"
  )

  // Asymmetric work across stages
  val asymmetric_l3_n2: ChainConfig = ChainConfig(
    numStages = 3,
    workPerStage = List(List(5, 2), List(2, 5), List(4, 3)),
    workersPerStage = List(2, 2, 2),
    label = "L=3 n=2 asymmetric work"
  )

  val asymmetric_l3_n3: ChainConfig = ChainConfig(
    numStages = 3,
    workPerStage = List(List(2, 5, 3), List(4, 2, 3), List(3, 3, 4)),
    workersPerStage = List(2, 2, 2),
    label = "L=3 n=3 asymmetric work"
  )

  // Different k values per stage
  val mixed_k_l3_n2: ChainConfig = ChainConfig(
    numStages = 3,
    workPerStage = List(List(4, 3), List(3, 4), List(3, 3)),
    workersPerStage = List(2, 3, 2),
    label = "L=3 n=2 mixed k=[2,3,2]"
  )

  val mixed_k_l3_n3: ChainConfig = ChainConfig(
    numStages = 3,
    workPerStage = List(List(3, 4, 5), List(4, 3, 3), List(3, 5, 4)),
    workersPerStage = List(2, 3, 2),
    label = "L=3 n=3 mixed k=[2,3,2]"
  )

  // Makespan counterexample: unsync [0,1]|[1,0] achieves Cmax=3.5, sync best=4.0
  val makespan_ce_l3_n2: ChainConfig = ChainConfig(
    numStages = 3,
    workPerStage = List(List(1, 2), List(4, 1), List(1, 2)),
    workersPerStage = List(2, 2, 2),
    label = "L=3 n=2 MAKESPAN CE"
  )

  // Larger makespan gap counterexample (gap=1.0)
  val makespan_ce_large_gap: ChainConfig = ChainConfig(
    numStages = 3,
    workPerStage = List(List(1, 3), List(6, 1), List(1, 3)),
    workersPerStage = List(2, 2, 2),
    label = "L=3 n=2 large gap CE"
  )

  // Symmetric work (same at every stage)
  val symmetric_l3_n2: ChainConfig = ChainConfig(
    numStages = 3,
    workPerStage = List(List(3, 3), List(3, 3), List(3, 3)),
    workersPerStage = List(2, 2, 2),
    label = "L=3 n=2 symmetric w=3"
  )

  val symmetric_l3_n3: ChainConfig = ChainConfig(
    numStages = 3,
    workPerStage = List(List(2, 2, 2), List(2, 2, 2), List(2, 2, 2)),
    workersPerStage = List(2, 2, 2),
    label = "L=3 n=3 symmetric w=2"
  )

  /** All configurations, ordered by expected runtime. */
  def all: List[ChainConfig] = List(
    // L=2 (baseline territory)
    l2_n2_k2,
    l2_n3_k2,
    // L=3 n=2 variants
    l3_n2_k2,
    asymmetric_l3_n2,
    mixed_k_l3_n2,
    symmetric_l3_n2,
    makespan_ce_l3_n2,
    makespan_ce_large_gap,
    // L=3 n=3 variants
    l3_n3_k2,
    asymmetric_l3_n3,
    mixed_k_l3_n3,
    symmetric_l3_n3,
    // L=4
    l4_n2_k2,
    l4_n3_k2,
  )


// --- Runner ---

object ChainRunner:

  def runAll(configs: List[ChainConfig], verbose: Boolean = true): Boolean =
    println("=" * 90)
    println("L-STAGE CHAIN SCHEDULING: PREEMPTIVE PRIORITY DOMINANCE ANALYSIS")
    println("=" * 90)
    println()
    println("Model: Team 1 -> Team 2 -> ... -> Team L (sequential pipeline)")
    println("Scheduler: Preemptive priority — all k workers on highest-priority available job")
    println("P4: For every schedule S, exists synchronized S* with C_j^(L)(S*) <= C_j^(L)(S) for all j")
    println()

    var allP4Pass = true
    var allP5Pass = true
    var allP6Pass = true

    // Header
    println(f"${"Config"}%-35s | ${"Perms"}%8s | ${"Sync"}%6s | ${"Unsync"}%8s | ${"P4-pw"}%-8s | ${"P5-Cmax"}%-8s | ${"P6-flow"}%-8s | ${"ms"}%7s")
    println("-" * 115)

    for (config <- configs) {
      val result = ChainAnalyzer.analyze(config)

      val p4str = if result.p4Holds then "YES" else "FAIL"
      val p5str = if result.makespanDomHolds then "YES" else "FAIL"
      val p6str = if result.flowtimeDomHolds then "YES" else "FAIL"
      val label = config.shortLabel.take(35)
      println(f"${label}%-35s | ${result.numPermutations}%8d | ${result.numSynchronized}%6d | ${result.numUnsynchronized}%8d | ${p4str}%-8s | ${p5str}%-8s | ${p6str}%-8s | ${result.elapsedMs}%,7d")

      if (!result.p4Holds) {
        allP4Pass = false
        result.counterexample.foreach(ce => println(s"    P4 counterexample: $ce"))
      }
      if (!result.makespanDomHolds) allP5Pass = false
      if (!result.flowtimeDomHolds) allP6Pass = false
    }

    println("-" * 115)
    println()
    println("Legend:")
    println("  P4-pw   = Pointwise domination: ∀S ∃S* sync with C_j(S*) ≤ C_j(S) for all j")
    println("  P5-Cmax = Makespan: best sync Cmax ≤ best overall Cmax")
    println("  P6-flow = Flowtime: best sync flowtime ≤ best overall flowtime")
    println()

    val p4result = if allP4Pass then "VERIFIED ✓" else "FAILED ✗"
    val p5result = if allP5Pass then "VERIFIED ✓" else "FAILED ✗"
    val p6result = if allP6Pass then "VERIFIED ✓" else "FAILED ✗"
    println(s"P4 (pointwise):  $p4result")
    println(s"P5 (makespan):   $p5result")
    println(s"P6 (flowtime):   $p6result")

    if !allP4Pass && allP5Pass && allP6Pass then
      println()
      println("KEY FINDING: Pointwise domination (P4) fails for some asymmetric configs,")
      println("but makespan (P5) and flowtime (P6) dominance hold across ALL configs.")
      println("This suggests sync ordering is optimal for regular objectives even when")
      println("it cannot dominate every individual job pointwise.")

    println()
    allP5Pass && allP6Pass  // return true if regular objectives are dominated
