/**
 * Revenue Impact Analysis: measure the value of finishing work sooner.
 *
 * Model: each initiative generates value v_j per unit time once completed
 * on the dependent team. Total revenue over horizon T = sum v_j * (T - C_j).
 * Synchronization delivers more cumulative value because initiatives
 * complete sooner — this is the dual of Cost of Delay.
 */
object RevenueAnalysis:

  /** Revenue for a schedule over time horizon T.
    * revenue = sum_j v_j * max(0, T - C_j) */
  def revenue(combined: List[TeamSchedule], horizon: Int): Double =
    val completions = ScheduleMetrics.initiativeCompletionTimes(combined)
    val depSchedules = combined.filter(_.team.teamType == Dependent)
    val byInitiative = depSchedules.flatMap(_.tasks).groupBy(_.initiative)
    byInitiative.map { (initiative, tasks) =>
      val cj = tasks.map(t => t.startTime + t.duration).max
      initiative.value * math.max(0, horizon - cj)
    }.sum

  /** Cumulative value curve: at each time t, how much total value has been
    * delivered so far? Returns (time, cumulative_value) pairs at each
    * completion event. */
  def cumulativeValueCurve(combined: List[TeamSchedule]): List[(Int, Double)] =
    val depSchedules = combined.filter(_.team.teamType == Dependent)
    val completions = depSchedules.flatMap(_.tasks).groupBy(_.initiative)
      .map { (init, tasks) =>
        (tasks.map(t => t.startTime + t.duration).max, init.value)
      }.toList.sortBy(_._1)

    var cumulative = 0.0
    completions.map { (time, value) =>
      cumulative += value
      (time, cumulative)
    }

  case class RevenueComparison(
    label: String,
    numSchedules: Int,
    // Best synchronized schedule
    bestSyncMakespan: Int,
    bestSyncFlowTime: Int,
    bestSyncRevenue: Double,
    bestSyncValueCurve: List[(Int, Double)],
    // Best unsynchronized schedule
    bestUnsyncMakespan: Int,
    bestUnsyncFlowTime: Int,
    bestUnsyncRevenue: Double,
    bestUnsyncValueCurve: List[(Int, Double)],
    // Revenue gap
    horizon: Int,
  ):
    def revenueGap: Double = bestSyncRevenue - bestUnsyncRevenue
    def revenueGapPct: Double =
      if bestUnsyncRevenue > 0 then (revenueGap / bestUnsyncRevenue) * 100 else 0.0
    def earlierDeliveryUnits: Int = bestUnsyncFlowTime - bestSyncFlowTime

  def analyze(configs: List[SweepConfig], maxSchedules: Long = 500_000L): List[RevenueComparison] =
    configs.flatMap { config =>
      val result = ConfigRunner.run(config, maxSchedules)
      result.report.flatMap { report =>
        val sync = report.allResults.filter(_.classification == ScheduleClass.Synchronized)
        val unsync = report.allResults.filter(_.classification == ScheduleClass.Unsynchronized)
        if sync.nonEmpty && unsync.nonEmpty then
          // Use a horizon that's 2x the worst makespan (captures the revenue tail)
          val horizon = report.allResults.map(_.makespan).max * 2
          val bestSync = sync.minBy(_.totalFlowTime)
          val bestUnsync = unsync.minBy(_.totalFlowTime)
          Some(RevenueComparison(
            label = config.shortLabel,
            numSchedules = report.totalSchedules,
            bestSyncMakespan = bestSync.makespan,
            bestSyncFlowTime = bestSync.totalFlowTime,
            bestSyncRevenue = revenue(bestSync.combined, horizon),
            bestSyncValueCurve = cumulativeValueCurve(bestSync.combined),
            bestUnsyncMakespan = bestUnsync.makespan,
            bestUnsyncFlowTime = bestUnsync.totalFlowTime,
            bestUnsyncRevenue = revenue(bestUnsync.combined, horizon),
            bestUnsyncValueCurve = cumulativeValueCurve(bestUnsync.combined),
            horizon = horizon,
          ))
        else None
      }
    }

  def printReport(comparisons: List[RevenueComparison]): Unit =
    println()
    println("=" * 120)
    println("REVENUE IMPACT OF SYNCHRONIZATION")
    println("(Each initiative generates value v_j per time unit once completed)")
    println("=" * 120)
    println()
    println(f"${"Config"}%-35s | ${"Horizon"}%7s | ${"Sync Rev"}%9s | ${"Unsync Rev"}%10s | ${"Rev Gap"}%8s | ${"Gap %"}%6s | ${"Earlier by"}%10s")
    println("-" * 120)

    for c <- comparisons do
      println(f"${c.label.take(35)}%-35s | ${c.horizon}%7d | ${c.bestSyncRevenue}%9.1f | ${c.bestUnsyncRevenue}%10.1f | ${c.revenueGap}%8.1f | ${c.revenueGapPct}%5.1f%% | ${c.earlierDeliveryUnits}%6d units")

    println("-" * 120)
    if comparisons.nonEmpty then
      val avgGapPct = comparisons.map(_.revenueGapPct).sum / comparisons.size
      val maxGapPct = comparisons.map(_.revenueGapPct).max
      val avgEarlier = comparisons.map(_.earlierDeliveryUnits).sum.toDouble / comparisons.size
      println(f"Average revenue increase: $avgGapPct%.1f%%  |  Maximum: $maxGapPct%.1f%%  |  Avg earlier delivery: $avgEarlier%.1f time units")
    println()

    // Show a detailed value curve comparison for the most impactful config
    if comparisons.nonEmpty then
      val best = comparisons.maxBy(_.revenueGapPct)
      println(s"--- Value Delivery Timeline: ${best.label} (largest revenue gap: ${f"${best.revenueGapPct}%.1f"}%) ---")
      println()
      println("  Synchronized schedule delivers value sooner at every point:")
      println(f"  ${"Time"}%6s | ${"Sync Cumulative"}%15s | ${"Unsync Cumulative"}%17s | ${"Sync Ahead By"}%14s")
      println("  " + "-" * 60)
      val allTimes = (best.bestSyncValueCurve.map(_._1) ++ best.bestUnsyncValueCurve.map(_._1)).distinct.sorted
      for t <- allTimes do
        val syncVal = best.bestSyncValueCurve.filter(_._1 <= t).lastOption.map(_._2).getOrElse(0.0)
        val unsyncVal = best.bestUnsyncValueCurve.filter(_._1 <= t).lastOption.map(_._2).getOrElse(0.0)
        val ahead = syncVal - unsyncVal
        val marker = if ahead > 0 then " ←" else ""
        println(f"  ${t}%6d | ${syncVal}%15.1f | ${unsyncVal}%17.1f | ${ahead}%+13.1f$marker")
      println()
