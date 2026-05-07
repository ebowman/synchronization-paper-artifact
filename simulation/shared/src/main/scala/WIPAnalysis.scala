/**
 * WIP Analysis: measure the emergent WIP reduction from synchronization.
 *
 * For each configuration, computes average WIP for the best synchronized
 * schedule vs the best unsynchronized schedule, and reports the reduction.
 */
object WIPAnalysis:

  case class WIPComparison(
    label: String,
    numSchedules: Int,
    bestSyncAvgWIP: Double,
    bestUnsyncAvgWIP: Double,
    avgSyncAvgWIP: Double,
    avgUnsyncAvgWIP: Double,
    bestSyncFlowTime: Int,
    bestUnsyncFlowTime: Int,
  ):
    def wipReductionPct: Double =
      if bestUnsyncAvgWIP > 0 then (1.0 - bestSyncAvgWIP / bestUnsyncAvgWIP) * 100 else 0.0
    def flowTimeReductionPct: Double =
      if bestUnsyncFlowTime > 0 then (1.0 - bestSyncFlowTime.toDouble / bestUnsyncFlowTime) * 100 else 0.0

  def analyze(configs: List[SweepConfig], maxSchedules: Long = 500_000L): List[WIPComparison] =
    configs.flatMap { config =>
      val result = ConfigRunner.run(config, maxSchedules)
      result.report.map { report =>
        val sync = report.allResults.filter(_.classification == ScheduleClass.Synchronized)
        val unsync = report.allResults.filter(_.classification == ScheduleClass.Unsynchronized)
        if sync.nonEmpty && unsync.nonEmpty then
          Some(WIPComparison(
            label = config.shortLabel,
            numSchedules = report.totalSchedules,
            bestSyncAvgWIP = sync.map(_.averageWIP).min,
            bestUnsyncAvgWIP = unsync.map(_.averageWIP).min,
            avgSyncAvgWIP = sync.map(_.averageWIP).sum / sync.size,
            avgUnsyncAvgWIP = unsync.map(_.averageWIP).sum / unsync.size,
            bestSyncFlowTime = sync.map(_.totalFlowTime).min,
            bestUnsyncFlowTime = unsync.map(_.totalFlowTime).min,
          ))
        else None
      }.flatten
    }

  def printReport(comparisons: List[WIPComparison]): Unit =
    println()
    println("=" * 110)
    println("EMERGENT WIP REDUCTION FROM SYNCHRONIZATION")
    println("=" * 110)
    println()
    println(f"${"Config"}%-35s | ${"#Sched"}%8s | ${"Sync WIP"}%8s | ${"Unsync WIP"}%10s | ${"WIP Δ"}%6s | ${"FlowTime Δ"}%10s")
    println("-" * 110)

    for c <- comparisons do
      println(f"${c.label.take(35)}%-35s | ${c.numSchedules}%8d | ${c.bestSyncAvgWIP}%8.2f | ${c.bestUnsyncAvgWIP}%10.2f | ${c.wipReductionPct}%5.1f%% | ${c.flowTimeReductionPct}%9.1f%%")

    println("-" * 110)
    if comparisons.nonEmpty then
      val avgReduction = comparisons.map(_.wipReductionPct).sum / comparisons.size
      val maxReduction = comparisons.map(_.wipReductionPct).max
      println(f"Average WIP reduction: $avgReduction%.1f%%  |  Maximum: $maxReduction%.1f%%")
      println()
      println("WIP reduction is an EMERGENT property of priority synchronization.")
      println("No explicit WIP limits are set — the shared priority list IS the WIP limit.")
    println()
