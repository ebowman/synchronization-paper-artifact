/**
 * Schedule Analysis Framework for Priority-Ordering Dominance Proof
 *
 * Problem Classification (Graham/Pinedo three-field notation):
 *   FH2(Pm, P1) | assembly, controllable p | Cmax
 *
 * A two-stage assembly flow shop with malleable jobs:
 *   - Stage 1: m identical parallel machines (foundation teams), each with k workers
 *   - Stage 2: 1 machine (dependent team) with k workers
 *   - Assembly constraint: a job cannot enter stage 2 until ALL stage-1 machines complete it
 *   - Jobs have controllable processing times (work divisible across workers)
 *
 * Key references:
 *   - Potts et al. (1995) "The two-stage assembly scheduling problem"
 *   - Lee & Vairaktarakis (1994) assembly flow shop permutation optimality
 *   - Johnson (1954) two-machine flow shop optimal scheduling
 *   - Pinedo (2016) Scheduling: Theory, Algorithms, and Systems, Ch. 8 & 17
 *   - Conway, Maxwell & Miller (1967) Theory of Scheduling
 */

// --- Classification ---

enum ScheduleClass:
  case Synchronized, Unsynchronized

object ScheduleClassifier:

  /** A combined schedule is "synchronized" iff every Foundation team
    * processes initiatives in the same order.
    *
    * The dependent team's ordering is NOT part of the classification —
    * it is a consequence of upstream completion times, not an independent choice.
    */
  def classify(combined: List[TeamSchedule]): ScheduleClass =
    val foundationSchedules = combined.filter(_.team.teamType == Foundation)
    val orderings = foundationSchedules.map(initiativeOrder)
    if orderings.distinct.size <= 1 then ScheduleClass.Synchronized
    else ScheduleClass.Unsynchronized

  /** Extract the initiative ordering from a TeamSchedule by finding
    * the earliest start time of each initiative across all tasks. */
  def initiativeOrder(ts: TeamSchedule): List[String] =
    ts.tasks
      .groupBy(_.initiative.name)
      .view.mapValues(_.map(_.startTime).min)
      .toList
      .sortBy(_._2)
      .map(_._1)

  /** Extract the work distribution profile from a combined schedule.
    * This is the set of (initiative, work-per-member) assignments,
    * used to control for work distribution when comparing orderings.
    *
    * Returns a canonical key that is identical for schedules with
    * the same work allocation, regardless of initiative ordering. */
  def workDistributionKey(combined: List[TeamSchedule]): String =
    combined.map { ts =>
      val byInitiative = ts.tasks
        .groupBy(_.initiative.name)
        .toList.sortBy(_._1)
        .map { (name, tasks) =>
          val durations = tasks.map(_.duration).sorted
          s"$name:${durations.mkString(",")}"
        }
      s"${ts.team.name}[${byInitiative.mkString(";")}]"
    }.sorted.mkString("|")


// --- Metrics ---

object ScheduleMetrics:

  /** Cmax (makespan): wall-clock time when ALL work across ALL teams finishes.
    * In this assembly flow shop, this always equals the dependent team's totalTime. */
  def makespan(combined: List[TeamSchedule]): Int =
    combined.map(_.totalTime).max

  /** Per-initiative completion time on the dependent (final) stage.
    * This is when each initiative is fully done end-to-end. */
  def initiativeCompletionTimes(combined: List[TeamSchedule]): Map[String, Int] =
    val dependentSchedules = combined.filter(_.team.teamType == Dependent)
    dependentSchedules.flatMap(_.tasks).groupBy(_.initiative.name)
      .view.mapValues(tasks => tasks.map(t => t.startTime + t.duration).max)
      .toMap

  /** Total flow time: sum of per-initiative completion times on the dependent stage.
    * Measures aggregate initiative delivery speed. */
  def totalFlowTime(combined: List[TeamSchedule]): Int =
    initiativeCompletionTimes(combined).values.sum

  /** Weighted completion time: sum over all initiatives of (value_j * completionTime_j)
    * on the dependent (final) stage. When all values are 1.0, this equals totalFlowTime. */
  def weightedCompletionTime(combined: List[TeamSchedule]): Double =
    val depSchedules = combined.filter(_.team.teamType == Dependent)
    val byInitiative = depSchedules.flatMap(_.tasks).groupBy(_.initiative)
    byInitiative.map { (initiative, tasks) =>
      initiative.value * tasks.map(t => t.startTime + t.duration).max
    }.sum

  /** Foundation span: max completion time across foundation teams only.
    * Isolates upstream cost from downstream cost. */
  def foundationSpan(combined: List[TeamSchedule]): Int =
    combined.filter(_.team.teamType == Foundation).map(_.totalTime).max

  /** Dependent team idle time: total time the dependent team waits
    * for upstream handoffs. This is the mechanism that explains WHY
    * synchronized ordering wins — it minimizes blocking at the
    * assembly (fork-join) barrier.
    *
    * Computed as: for each task on the dependent team, the gap between
    * the earliest it could start (upstream completion) and when it actually starts. */
  def dependentIdleTime(combined: List[TeamSchedule]): Int =
    val dependentSchedules = combined.filter(_.team.teamType == Dependent)
    val allDependentTasks = dependentSchedules.flatMap(_.tasks)
    if allDependentTasks.isEmpty then return 0

    // Find the earliest start across all dependent tasks (the pipeline start for stage 2)
    val sortedByStart = allDependentTasks.sortBy(_.startTime)
    val firstStart = sortedByStart.head.startTime

    // Idle time = dependent team's total span minus actual work time
    val dependentMakespan = dependentSchedules.map(_.totalTime).max
    val totalWorkTime = allDependentTasks.map(_.duration).sum
    val totalSpan = dependentMakespan - firstStart
    // Each member's span contributes; idle = total member-time minus work-time
    val numMembers = dependentSchedules.flatMap(_.team.members).distinct.size
    val totalMemberTime = numMembers * totalSpan
    totalMemberTime - totalWorkTime

  /** Time-integrated WIP = sum of per-initiative completion times on the dependent team.
    * By the standard identity: integral of WIP(t) dt = sum_j C_j^{(2)}.
    * This equals totalFlowTime when all jobs are released at time 0. */
  def integratedWIP(combined: List[TeamSchedule]): Int =
    totalFlowTime(combined)

  /** Peak WIP: maximum number of initiatives simultaneously in-flight at any time.
    * An initiative is in-flight from time 0 until it completes on the dependent team. */
  def peakWIP(combined: List[TeamSchedule]): Int =
    val completions = initiativeCompletionTimes(combined)
    if completions.isEmpty then return 0
    val maxTime = completions.values.max
    // At time t, WIP = number of initiatives with C_j > t
    // WIP starts at n (all in-flight) and decreases by 1 at each completion
    // Peak WIP = n (at time 0). But the interesting metric is:
    // how quickly does WIP decrease? Let's measure the WIP at the midpoint
    // and the time at which WIP drops below n/2.
    // Actually: peak WIP is always n when all start at t=0.
    // The more useful metric: average WIP = integratedWIP / makespan
    completions.size  // Always n for this model

  /** Average WIP = time-integrated WIP / makespan.
    * By Little's Law: L = lambda * W, where lambda = n/Cmax and W = avg flow time. */
  def averageWIP(combined: List[TeamSchedule]): Double =
    val cmax = makespan(combined)
    if cmax == 0 then 0.0
    else integratedWIP(combined).toDouble / cmax

  /** WIP at each completion event: returns the WIP level after each initiative completes.
    * Useful for comparing how quickly the system drains. */
  def wipProfile(combined: List[TeamSchedule]): List[(Int, Int)] =
    val completions = initiativeCompletionTimes(combined).values.toList.sorted
    val n = completions.size
    completions.zipWithIndex.map { (time, idx) => (time, n - idx - 1) }


// --- Result Types ---

case class ScheduleResult(
  combined: List[TeamSchedule],
  classification: ScheduleClass,
  makespan: Int,
  totalFlowTime: Int,
  weightedCompletionTime: Double,
  foundationSpan: Int,
  dependentIdleTime: Int,
  averageWIP: Double,
  workDistributionKey: String,
  foundationOrderings: List[List[String]],
  initiativeCompletionTimes: Map[String, Int]
)

case class PartitionSummary(
  classification: ScheduleClass,
  count: Int,
  bestMakespan: Int,
  worstMakespan: Int,
  avgMakespan: Double,
  bestFlowTime: Int,
  worstFlowTime: Int,
  avgDependentIdleTime: Double
)

case class WorkDistributionComparison(
  workDistributionKey: String,
  syncCount: Int,
  unsyncCount: Int,
  bestSyncMakespan: Int,
  worstSyncMakespan: Int,
  bestUnsyncMakespan: Int,
  worstUnsyncMakespan: Int,
  syncDominates: Boolean  // worst sync <= best unsync
)

case class AnalysisReport(
  totalSchedules: Int,
  partitions: Map[ScheduleClass, PartitionSummary],
  workDistributionComparisons: List[WorkDistributionComparison],
  // P1a (strong): ALL optimal schedules are synchronized
  optimalAlwaysSynchronized: Boolean,
  // P1b (weak, the key claim): there EXISTS a synchronized schedule at the optimum
  //   i.e., synchronization is never suboptimal — you never need to desynchronize
  optimalIncludesSynchronized: Boolean,
  // P1b-wct: among schedules that minimize weighted completion time,
  //   there EXISTS a synchronized schedule
  weightedOptimalIncludesSynchronized: Boolean,
  // P2: within every work distribution class, sync dominates
  syncDominatesWithinAllDistributions: Boolean,
  // P3: worst sync makespan <= best unsync makespan (across all distributions)
  syncDominatesOverall: Boolean,
  // P4 (pointwise domination — the paper's main theorem):
  //   For EVERY schedule S, there EXISTS a synchronized schedule S* such that
  //   C^(2)_j(S*) <= C^(2)_j(S) for every initiative j.
  pointwiseDominationHolds: Boolean,
  allResults: List[ScheduleResult]
)


// --- Analyzer ---

object ScheduleAnalyzer:

  def analyze(allSchedules: List[List[TeamSchedule]]): AnalysisReport =
    val results = allSchedules.map { combined =>
      ScheduleResult(
        combined = combined,
        classification = ScheduleClassifier.classify(combined),
        makespan = ScheduleMetrics.makespan(combined),
        totalFlowTime = ScheduleMetrics.totalFlowTime(combined),
        weightedCompletionTime = ScheduleMetrics.weightedCompletionTime(combined),
        foundationSpan = ScheduleMetrics.foundationSpan(combined),
        dependentIdleTime = ScheduleMetrics.dependentIdleTime(combined),
        averageWIP = ScheduleMetrics.averageWIP(combined),
        workDistributionKey = ScheduleClassifier.workDistributionKey(combined),
        foundationOrderings = combined
          .filter(_.team.teamType == Foundation)
          .map(ScheduleClassifier.initiativeOrder),
        initiativeCompletionTimes = ScheduleMetrics.initiativeCompletionTimes(combined)
      )
    }

    // Partition by classification
    val byClass = results.groupBy(_.classification)
    val summaries = byClass.map { (cls, group) =>
      val makespans = group.map(_.makespan)
      val flowTimes = group.map(_.totalFlowTime)
      val idleTimes = group.map(_.dependentIdleTime)
      cls -> PartitionSummary(
        classification = cls,
        count = group.size,
        bestMakespan = makespans.min,
        worstMakespan = makespans.max,
        avgMakespan = makespans.sum.toDouble / makespans.size,
        bestFlowTime = flowTimes.min,
        worstFlowTime = flowTimes.max,
        avgDependentIdleTime = idleTimes.sum.toDouble / idleTimes.size
      )
    }

    // Work distribution controlled comparisons
    val byDistribution = results.groupBy(_.workDistributionKey)
    val distComparisons = byDistribution.toList.map { (distKey, group) =>
      val synced = group.filter(_.classification == ScheduleClass.Synchronized)
      val unsynced = group.filter(_.classification == ScheduleClass.Unsynchronized)
      WorkDistributionComparison(
        workDistributionKey = distKey,
        syncCount = synced.size,
        unsyncCount = unsynced.size,
        bestSyncMakespan = if synced.nonEmpty then synced.map(_.makespan).min else Int.MaxValue,
        worstSyncMakespan = if synced.nonEmpty then synced.map(_.makespan).max else Int.MaxValue,
        bestUnsyncMakespan = if unsynced.nonEmpty then unsynced.map(_.makespan).min else Int.MinValue,
        worstUnsyncMakespan = if unsynced.nonEmpty then unsynced.map(_.makespan).max else Int.MinValue,
        syncDominates = synced.nonEmpty && unsynced.nonEmpty &&
          synced.map(_.makespan).max <= unsynced.map(_.makespan).min
      )
    }

    // Proof checks
    val globalOptimalMakespan = results.map(_.makespan).min
    val optimalSchedules = results.filter(_.makespan == globalOptimalMakespan)
    val optimalAlwaysSynced = optimalSchedules.forall(_.classification == ScheduleClass.Synchronized)
    val optimalIncludesSynced = optimalSchedules.exists(_.classification == ScheduleClass.Synchronized)

    // Weighted completion time P1b check
    val globalOptimalWCT = results.map(_.weightedCompletionTime).min
    val wctOptimalSchedules = results.filter(_.weightedCompletionTime == globalOptimalWCT)
    val wctOptimalIncludesSynced = wctOptimalSchedules.exists(_.classification == ScheduleClass.Synchronized)

    val mixedDistributions = distComparisons.filter(d => d.syncCount > 0 && d.unsyncCount > 0)
    val syncDominatesAll = mixedDistributions.forall(_.syncDominates)

    val syncResults = results.filter(_.classification == ScheduleClass.Synchronized)
    val unsyncResults = results.filter(_.classification == ScheduleClass.Unsynchronized)
    val syncDominatesOverall = syncResults.nonEmpty && unsyncResults.nonEmpty &&
      syncResults.map(_.makespan).max <= unsyncResults.map(_.makespan).min

    // P4: Pointwise domination (the paper's main theorem)
    // For every schedule S, there exists a synchronized schedule S* such that
    // C^(2)_j(S*) <= C^(2)_j(S) for every initiative j.
    val pointwiseDomination = results.forall { s =>
      syncResults.exists { sStar =>
        s.initiativeCompletionTimes.forall { (job, cj) =>
          sStar.initiativeCompletionTimes.get(job).exists(_ <= cj)
        }
      }
    }

    AnalysisReport(
      totalSchedules = results.size,
      partitions = summaries,
      workDistributionComparisons = distComparisons,
      optimalAlwaysSynchronized = optimalAlwaysSynced,
      optimalIncludesSynchronized = optimalIncludesSynced,
      weightedOptimalIncludesSynchronized = wctOptimalIncludesSynced,
      syncDominatesWithinAllDistributions = syncDominatesAll,
      syncDominatesOverall = syncDominatesOverall,
      pointwiseDominationHolds = pointwiseDomination,
      allResults = results
    )

  def printReport(report: AnalysisReport): Unit =
    println("=" * 78)
    println("PRIORITY ORDERING DOMINANCE ANALYSIS")
    println("Problem: FH2(Pm, P1) | assembly, controllable p | Cmax")
    println("=" * 78)
    println()
    println(s"Total schedules enumerated: ${report.totalSchedules}")
    println()

    // Full schedule table
    println("--- Complete Schedule Enumeration ---")
    println(f"${"#"}%3s | ${"Class"}%-14s | ${"Cmax"}%4s | ${"FlowTime"}%8s | ${"WCT"}%8s | ${"FndSpan"}%7s | ${"IdleTime"}%8s | Foundation Orderings")
    println("-" * 100)
    for (r, i) <- report.allResults.sortBy(r => (r.makespan, r.classification.ordinal)).zipWithIndex do
      val cls = r.classification.toString
      val orderings = r.foundationOrderings.map(_.mkString("→")).mkString(" | ")
      println(f"${i+1}%3d | ${cls}%-14s | ${r.makespan}%4d | ${r.totalFlowTime}%8d | ${r.weightedCompletionTime}%8.1f | ${r.foundationSpan}%7d | ${r.dependentIdleTime}%8d | $orderings")
    println()

    // Partition summaries with WIP
    println("--- Partition Summaries ---")
    for (cls, summary) <- report.partitions.toList.sortBy(_._1.ordinal) do
      val wips = report.allResults.filter(_.classification == cls).map(_.averageWIP)
      println(s"${cls}:")
      println(f"  Count: ${summary.count}, Makespan: best=${summary.bestMakespan}, worst=${summary.worstMakespan}, avg=${summary.avgMakespan}%.1f")
      println(f"  FlowTime: best=${summary.bestFlowTime}, worst=${summary.worstFlowTime}")
      println(f"  Avg dependent idle time: ${summary.avgDependentIdleTime}%.1f")
      if wips.nonEmpty then
        println(f"  Average WIP: best=${wips.min}%.2f, worst=${wips.max}%.2f, avg=${wips.sum / wips.size}%.2f")
    println()

    // Work distribution controlled comparisons
    if report.workDistributionComparisons.exists(d => d.syncCount > 0 && d.unsyncCount > 0) then
      println("--- Work Distribution Controlled Comparisons ---")
      for comp <- report.workDistributionComparisons if comp.syncCount > 0 && comp.unsyncCount > 0 do
        println(s"Distribution: ${comp.workDistributionKey}")
        println(f"  Synchronized:   best=${comp.bestSyncMakespan}, worst=${comp.worstSyncMakespan} (n=${comp.syncCount})")
        println(f"  Unsynchronized: best=${comp.bestUnsyncMakespan}, worst=${comp.worstUnsyncMakespan} (n=${comp.unsyncCount})")
        val dom = if comp.syncDominates then "YES ✓" else "NO ✗"
        println(s"  Sync dominates (worst sync ≤ best unsync): $dom")
      println()

    // Proof results
    println("=" * 78)
    println("PROOF RESULTS")
    println("=" * 78)
    val p1a = if report.optimalAlwaysSynchronized then "VERIFIED ✓" else "FAILED ✗"
    println(s"  P1a: ALL optimal schedules are synchronized:      $p1a")
    val p1b = if report.optimalIncludesSynchronized then "VERIFIED ✓" else "FAILED ✗"
    println(s"  P1b: Optimal INCLUDES a synchronized schedule:    $p1b")
    val p1bwct = if report.weightedOptimalIncludesSynchronized then "VERIFIED ✓" else "FAILED ✗"
    println(s"  P1b-wct: Weighted-optimal INCLUDES synchronized:  $p1bwct")
    val p2 = if report.syncDominatesWithinAllDistributions then "VERIFIED ✓" else "FAILED ✗"
    println(s"  P2:  Sync dominates within all dist. classes:     $p2")
    val p3 = if report.syncDominatesOverall then "VERIFIED ✓" else "FAILED ✗"
    println(s"  P3:  Sync dominates overall (strong dominance):   $p3")
    val p4 = if report.pointwiseDominationHolds then "VERIFIED ✓" else "FAILED ✗"
    println(s"  P4:  Pointwise domination (∀S ∃S* sync: ∀j C_j(S*) ≤ C_j(S)): $p4")
    println()
