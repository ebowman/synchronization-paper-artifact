import scala.scalajs.js
import scala.scalajs.js.annotation.*
import scala.scalajs.js.JSConverters.*

/**
 * Scala.js entry points for the browser frontend.
 *
 * All functions are exported as browser globals via @JSExportTopLevel.
 * Return types are js.Dictionary / js.Array for direct consumption from JavaScript.
 */
object SimulationAPI:

  // ============================================================
  // Assembly Flow Shop API
  // ============================================================

  /** Run a single assembly flow shop configuration and return full analysis.
    *
    * Usage from JS:
    *   const result = runAssemblyConfig([2,3,4], 2, 2);
    *   // result.proofResults.p4  => true
    *   // result.schedules[0].classification => "Synchronized"
    */
  @JSExportTopLevel("runAssemblyConfig")
  def runAssemblyConfig(
    workPerInitiative: js.Array[Int],
    numFoundationTeams: Int,
    teamSize: Int,
    valuePerInitiative: js.Array[Double] = js.Array(),
    workPerTeam: js.Array[js.Array[Int]] = js.Array()
  ): js.Dictionary[js.Any] =
    val config = SweepConfig(
      workPerInitiative = workPerInitiative.toList,
      numFoundationTeams = numFoundationTeams,
      teamSize = teamSize,
      valuePerInitiative = if valuePerInitiative.isEmpty then List.empty else valuePerInitiative.toList,
      workPerTeam = if workPerTeam.isEmpty then List.empty else workPerTeam.map(_.toList).toList
    )
    val result = ConfigRunner.run(config, maxSchedules = 2_000_000L)
    sweepResultToJS(result)

  /** Run a sweep across multiple configs, returning summary data. */
  @JSExportTopLevel("runAssemblySweep")
  def runAssemblySweep(configsJS: js.Array[js.Dictionary[js.Any]]): js.Dictionary[js.Any] =
    val configs = configsJS.map(jsConfigToSweepConfig).toList
    val summary = ConfigSweep.runAll(configs, verbose = false, maxSchedules = 2_000_000L)
    sweepSummaryToJS(summary)

  /** Get all standard preset configurations as a JS array. */
  @JSExportTopLevel("getAssemblyPresets")
  def getAssemblyPresets(): js.Dictionary[js.Any] =
    js.Dictionary(
      "symmetric" -> StandardConfigs.symmetric.map(sweepConfigToJS).toJSArray,
      "asymmetric" -> StandardConfigs.asymmetric.map(sweepConfigToJS).toJSArray,
      "valueWeighted" -> StandardConfigs.valueWeighted.map(sweepConfigToJS).toJSArray,
      "heterogeneous" -> StandardConfigs.heterogeneous.map(sweepConfigToJS).toJSArray,
      "quick" -> StandardConfigs.quick.map(sweepConfigToJS).toJSArray,
      "full" -> StandardConfigs.full.map(sweepConfigToJS).toJSArray,
    )

  // ============================================================
  // Chain Scheduling API
  // ============================================================

  /** Run a single chain configuration and return analysis. */
  @JSExportTopLevel("runChainConfig")
  def runChainConfig(
    workPerStage: js.Array[js.Array[Int]],
    workersPerStage: js.Array[Int]
  ): js.Dictionary[js.Any] =
    val config = ChainConfig(
      numStages = workPerStage.length,
      workPerStage = workPerStage.map(_.toList).toList,
      workersPerStage = workersPerStage.toList
    )
    chainResultToJS(ChainAnalyzer.analyze(config))

  /** Get all standard chain preset configurations. */
  @JSExportTopLevel("getChainPresets")
  def getChainPresets(): js.Array[js.Dictionary[js.Any]] =
    StandardChainConfigs.all.map(chainConfigToJS).toJSArray

  // ============================================================
  // WIP & Revenue Analysis API
  // ============================================================

  /** Run WIP analysis across preset configs. */
  @JSExportTopLevel("runWIPAnalysis")
  def runWIPAnalysis(configsJS: js.Array[js.Dictionary[js.Any]]): js.Array[js.Dictionary[js.Any]] =
    val configs = if configsJS.isEmpty then StandardConfigs.full
                  else configsJS.map(jsConfigToSweepConfig).toList
    val comparisons = WIPAnalysis.analyze(configs, maxSchedules = 2_000_000L)
    comparisons.map(wipComparisonToJS).toJSArray

  /** Run revenue analysis across preset configs. */
  @JSExportTopLevel("runRevenueAnalysis")
  def runRevenueAnalysis(configsJS: js.Array[js.Dictionary[js.Any]]): js.Array[js.Dictionary[js.Any]] =
    val configs = if configsJS.isEmpty then StandardConfigs.full
                  else configsJS.map(jsConfigToSweepConfig).toList
    val comparisons = RevenueAnalysis.analyze(configs, maxSchedules = 2_000_000L)
    comparisons.map(revenueComparisonToJS).toJSArray

  // ============================================================
  // Estimation (for UI: show expected computation cost)
  // ============================================================

  /** Estimate schedule count for a config without running it. */
  @JSExportTopLevel("estimateSchedules")
  def estimateSchedules(
    workPerInitiative: js.Array[Int],
    numFoundationTeams: Int,
    teamSize: Int
  ): Double =
    val config = SweepConfig(workPerInitiative.toList, numFoundationTeams, teamSize)
    ScheduleEstimator.estimateTotalSchedules(config).toDouble

  // ============================================================
  // Conversion helpers: Scala -> JS
  // ============================================================

  private def sweepConfigToJS(c: SweepConfig): js.Dictionary[js.Any] =
    js.Dictionary(
      "workPerInitiative" -> c.workPerInitiative.toJSArray,
      "numFoundationTeams" -> c.numFoundationTeams,
      "teamSize" -> c.teamSize,
      "label" -> c.shortLabel,
      "valuePerInitiative" -> (if c.valuePerInitiative.nonEmpty then c.valuePerInitiative.toJSArray else js.Array[Double]()),
      "workPerTeam" -> (if c.workPerTeam.nonEmpty then c.workPerTeam.map(_.toJSArray).toJSArray else js.Array[js.Array[Int]]()),
    )

  private def sweepResultToJS(r: SweepResult): js.Dictionary[js.Any] =
    val base = js.Dictionary[js.Any](
      "config" -> sweepConfigToJS(r.config),
      "scheduleCount" -> r.scheduleCount,
      "estimatedSchedules" -> r.estimatedSchedules.toDouble,
      "elapsedMs" -> r.elapsedMs.toDouble,
      "skipped" -> r.skipped,
      "skipReason" -> r.skipReason,
    )
    r.report.foreach { report =>
      base("proofResults") = js.Dictionary(
        "p1a" -> report.optimalAlwaysSynchronized,
        "p1b" -> report.optimalIncludesSynchronized,
        "p1bw" -> report.weightedOptimalIncludesSynchronized,
        "p2" -> report.syncDominatesWithinAllDistributions,
        "p3" -> report.syncDominatesOverall,
        "p4" -> report.pointwiseDominationHolds,
      )
      base("partitions") = partitionsToJS(report)
      base("schedules") = report.allResults.map(scheduleResultToJS).toJSArray
      base("totalSchedules") = report.totalSchedules
    }
    base

  private def partitionsToJS(report: AnalysisReport): js.Dictionary[js.Any] =
    val result = js.Dictionary[js.Any]()
    report.partitions.foreach { (cls, summary) =>
      result(cls.toString.toLowerCase) = js.Dictionary(
        "count" -> summary.count,
        "bestMakespan" -> summary.bestMakespan,
        "worstMakespan" -> summary.worstMakespan,
        "avgMakespan" -> summary.avgMakespan,
        "bestFlowTime" -> summary.bestFlowTime,
        "worstFlowTime" -> summary.worstFlowTime,
        "avgDependentIdleTime" -> summary.avgDependentIdleTime,
      )
    }
    result

  private def scheduleResultToJS(r: ScheduleResult): js.Dictionary[js.Any] =
    js.Dictionary(
      "classification" -> r.classification.toString,
      "makespan" -> r.makespan,
      "totalFlowTime" -> r.totalFlowTime,
      "weightedCompletionTime" -> r.weightedCompletionTime,
      "foundationSpan" -> r.foundationSpan,
      "dependentIdleTime" -> r.dependentIdleTime,
      "averageWIP" -> r.averageWIP,
      "foundationOrderings" -> r.foundationOrderings.map(_.toJSArray).toJSArray,
      "initiativeCompletionTimes" -> {
        val d = js.Dictionary[js.Any]()
        r.initiativeCompletionTimes.foreach { (k, v) => d(k) = v }
        d
      },
      // Detailed task data for Gantt chart visualization
      "teams" -> r.combined.map(teamScheduleToJS).toJSArray,
    )

  private def teamScheduleToJS(ts: TeamSchedule): js.Dictionary[js.Any] =
    js.Dictionary(
      "name" -> ts.team.name,
      "type" -> ts.team.teamType.toString,
      "totalTime" -> ts.totalTime,
      "members" -> ts.team.members.map(_.id).toJSArray,
      "tasks" -> ts.tasks.map(taskToJS).toJSArray,
    )

  private def taskToJS(t: Task): js.Dictionary[js.Any] =
    js.Dictionary(
      "initiative" -> t.initiative.name,
      "initiativeValue" -> t.initiative.value,
      "startTime" -> t.startTime,
      "duration" -> t.duration,
      "endTime" -> (t.startTime + t.duration),
      "members" -> t.assignedTeamMembers.map(_.id).toJSArray,
    )

  private def sweepSummaryToJS(s: SweepSummary): js.Dictionary[js.Any] =
    js.Dictionary(
      "allVerified" -> s.allVerified,
      "results" -> s.results.map(sweepResultToJS).toJSArray,
    )

  // Chain config/result conversion

  private def chainConfigToJS(c: ChainConfig): js.Dictionary[js.Any] =
    js.Dictionary(
      "numStages" -> c.numStages,
      "numJobs" -> c.numJobs,
      "workPerStage" -> c.workPerStage.map(_.toJSArray).toJSArray,
      "workersPerStage" -> c.workersPerStage.toJSArray,
      "label" -> c.shortLabel,
    )

  private def chainResultToJS(r: ChainAnalyzer.ChainResult): js.Dictionary[js.Any] =
    val d = js.Dictionary[js.Any](
      "config" -> chainConfigToJS(r.config),
      "p4Holds" -> r.p4Holds,
      "makespanDomHolds" -> r.makespanDomHolds,
      "flowtimeDomHolds" -> r.flowtimeDomHolds,
      "numPermutations" -> r.numPermutations,
      "numSynchronized" -> r.numSynchronized,
      "numUnsynchronized" -> r.numUnsynchronized,
      "elapsedMs" -> r.elapsedMs.toDouble,
    )
    r.counterexample.foreach { ce => d("counterexample") = ce }
    d

  // WIP comparison conversion

  private def wipComparisonToJS(c: WIPAnalysis.WIPComparison): js.Dictionary[js.Any] =
    js.Dictionary(
      "label" -> c.label,
      "numSchedules" -> c.numSchedules,
      "bestSyncAvgWIP" -> c.bestSyncAvgWIP,
      "bestUnsyncAvgWIP" -> c.bestUnsyncAvgWIP,
      "avgSyncAvgWIP" -> c.avgSyncAvgWIP,
      "avgUnsyncAvgWIP" -> c.avgUnsyncAvgWIP,
      "bestSyncFlowTime" -> c.bestSyncFlowTime,
      "bestUnsyncFlowTime" -> c.bestUnsyncFlowTime,
      "wipReductionPct" -> c.wipReductionPct,
      "flowTimeReductionPct" -> c.flowTimeReductionPct,
    )

  // Revenue comparison conversion

  private def revenueComparisonToJS(c: RevenueAnalysis.RevenueComparison): js.Dictionary[js.Any] =
    js.Dictionary(
      "label" -> c.label,
      "numSchedules" -> c.numSchedules,
      "horizon" -> c.horizon,
      "bestSyncMakespan" -> c.bestSyncMakespan,
      "bestSyncFlowTime" -> c.bestSyncFlowTime,
      "bestSyncRevenue" -> c.bestSyncRevenue,
      "bestSyncValueCurve" -> c.bestSyncValueCurve.map { (t, v) =>
        js.Dictionary[js.Any]("time" -> t, "value" -> v)
      }.toJSArray,
      "bestUnsyncMakespan" -> c.bestUnsyncMakespan,
      "bestUnsyncFlowTime" -> c.bestUnsyncFlowTime,
      "bestUnsyncRevenue" -> c.bestUnsyncRevenue,
      "bestUnsyncValueCurve" -> c.bestUnsyncValueCurve.map { (t, v) =>
        js.Dictionary[js.Any]("time" -> t, "value" -> v)
      }.toJSArray,
      "revenueGap" -> c.revenueGap,
      "revenueGapPct" -> c.revenueGapPct,
      "earlierDeliveryUnits" -> c.earlierDeliveryUnits,
    )

  // JS -> Scala conversion

  private def jsConfigToSweepConfig(d: js.Dictionary[js.Any]): SweepConfig =
    SweepConfig(
      workPerInitiative = d("workPerInitiative").asInstanceOf[js.Array[Int]].toList,
      numFoundationTeams = d("numFoundationTeams").asInstanceOf[Int],
      teamSize = d("teamSize").asInstanceOf[Int],
      label = d.getOrElse("label", "").asInstanceOf[String],
      valuePerInitiative = d.get("valuePerInitiative")
        .map(_.asInstanceOf[js.Array[Double]].toList)
        .filter(_.nonEmpty)
        .getOrElse(List.empty),
      workPerTeam = d.get("workPerTeam")
        .map(_.asInstanceOf[js.Array[js.Array[Int]]].map(_.toList).toList)
        .filter(_.nonEmpty)
        .getOrElse(List.empty),
    )
