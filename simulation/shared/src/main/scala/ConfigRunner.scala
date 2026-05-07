/**
 * Parameterized configuration runner and multi-configuration sweep.
 *
 * This module does NOT modify WorkDivisionGenerator or Analysis.scala.
 * It builds on them to support:
 *   - Running arbitrary (numInitiatives, workPerInitiative, numFoundationTeams, teamSize) configs
 *   - Asymmetric work sizes (e.g., w=[2,3,4])
 *   - Sweeping across multiple configs with a summary table
 *   - Schedule count estimation and safety limits to prevent OOM
 */

// --- Configuration ---

/** A single configuration to enumerate and analyze.
  *
  * @param workPerInitiative work required for each initiative (length = numInitiatives).
  *                          Asymmetric: e.g., List(2, 3, 4) means three initiatives
  *                          with different work amounts.
  * @param numFoundationTeams number of foundation (stage-1) teams.
  * @param teamSize           number of members per team (all teams same size).
  * @param label              optional human-readable label for reporting.
  */
case class SweepConfig(
  workPerInitiative: List[Int],
  numFoundationTeams: Int,
  teamSize: Int,
  label: String = "",
  valuePerInitiative: List[Double] = List.empty,  // empty = all 1.0
  /** Per-team work overrides: workPerTeam(teamIdx)(initIdx) = work.
    * If empty, all teams use workPerInitiative (homogeneous). */
  workPerTeam: List[List[Int]] = List.empty
):
  def numInitiatives: Int = workPerInitiative.size
  def totalWork: Int = workPerInitiative.sum
  def isHeterogeneous: Boolean = workPerTeam.nonEmpty

  /** Short descriptor used in summary tables. */
  def shortLabel: String =
    if label.nonEmpty then label
    else s"n=${numInitiatives} w=${workPerInitiative.mkString(",")} f=$numFoundationTeams k=$teamSize"

/** Result of running a single configuration through enumeration + analysis. */
case class SweepResult(
  config: SweepConfig,
  report: Option[AnalysisReport],  // None if skipped
  scheduleCount: Int,
  estimatedSchedules: Long,
  elapsedMs: Long,
  skipped: Boolean = false,
  skipReason: String = ""
)

/** Aggregate summary across all configurations. */
case class SweepSummary(
  results: List[SweepResult],
  allVerified: Boolean
)


// --- Schedule Count Estimation (Item 4) ---

object ScheduleEstimator:

  /** Estimate the total number of combined schedules for a configuration,
    * WITHOUT actually generating them. Used to bail out before OOM.
    */
  def estimateTotalSchedules(config: SweepConfig): Long =
    val k = config.teamSize
    val n = config.numInitiatives

    // n! (initiative permutations)
    val initPerms = factorial(n)

    // Product of compositions counts across all initiatives
    val compositionsProduct = config.workPerInitiative.map { w =>
      numCompositions(w, k)
    }.product

    // Schedules per team = initiative permutations * compositions product
    val schedulesPerTeam = initPerms * compositionsProduct

    // Foundation teams: cartesian product across all foundation teams
    val foundationCombinations = math.pow(schedulesPerTeam.toDouble, config.numFoundationTeams).toLong

    // Dependent team: for each foundation combination, one set of dependent schedules
    foundationCombinations * schedulesPerTeam

  /** Number of compositions of n into k positive parts = C(n-1, k-1). */
  private def numCompositions(n: Int, k: Int): Long =
    if n < k then 0L
    else binomial(n - 1, k - 1)

  private def binomial(n: Int, k: Int): Long =
    if k < 0 || k > n then 0L
    else if k == 0 || k == n then 1L
    else
      val k2 = math.min(k, n - k)
      (1 to k2).foldLeft(1L) { (acc, i) =>
        acc * (n - k2 + i) / i
      }

  private def factorial(n: Int): Long =
    (1 to n).foldLeft(1L)(_ * _)


// --- Configuration Runner ---

object ConfigRunner:

  /** Default maximum schedule count before we skip a configuration. */
  val DefaultMaxSchedules: Long = 500_000L

  /** Build teams, enumerate all schedules, analyze, and return the report. */
  def run(config: SweepConfig, maxSchedules: Long = DefaultMaxSchedules): SweepResult =
    val startTime = System.currentTimeMillis()

    // Validate: compositions(n, k) requires n >= k
    val infeasible = config.workPerInitiative.filter(_ < config.teamSize)
    if infeasible.nonEmpty then
      val elapsedMs = System.currentTimeMillis() - startTime
      return SweepResult(
        config = config,
        report = None,
        scheduleCount = 0,
        estimatedSchedules = 0L,
        elapsedMs = elapsedMs,
        skipped = true,
        skipReason = s"Infeasible: work values ${infeasible.mkString(",")} < teamSize=${config.teamSize}"
      )

    // Estimate schedule count and bail out if too large
    val estimated = ScheduleEstimator.estimateTotalSchedules(config)
    if estimated > maxSchedules then
      val elapsedMs = System.currentTimeMillis() - startTime
      return SweepResult(
        config = config,
        report = None,
        scheduleCount = 0,
        estimatedSchedules = estimated,
        elapsedMs = elapsedMs,
        skipped = true,
        skipReason = f"Estimated $estimated%,d schedules exceeds limit of $maxSchedules%,d"
      )

    // Build initiatives with potentially asymmetric work and values
    val values = if config.valuePerInitiative.nonEmpty then config.valuePerInitiative
                 else List.fill(config.numInitiatives)(1.0)
    val initiatives = config.workPerInitiative.zip(values).zipWithIndex.map { case ((work, value), idx) =>
      Initiative(s"Initiative ${('A' + idx).toChar}", work, value)
    }

    // Build foundation teams, each with `teamSize` members
    var nextMemberId = 1
    val foundationTeams = (1 to config.numFoundationTeams).toList.map { teamIdx =>
      val members = (0 until config.teamSize).toList.map { _ =>
        val m = TeamMember(nextMemberId)
        nextMemberId += 1
        m
      }
      // Build work overrides for heterogeneous configs
      val overrides: Map[String, Int] =
        if config.workPerTeam.nonEmpty then
          val teamWork = config.workPerTeam(teamIdx - 1)
          initiatives.zip(teamWork).map { (init, w) => init.name -> w }.toMap
        else Map.empty
      Team(
        name = s"Foundation Team $teamIdx",
        teamType = Foundation,
        members = members,
        initiatives = initiatives,
        workOverrides = overrides
      )
    }

    // Build one dependent team
    val dependentMembers = (0 until config.teamSize).toList.map { _ =>
      val m = TeamMember(nextMemberId)
      nextMemberId += 1
      m
    }
    val dependentTeam = Team(
      name = "Dependent Team",
      teamType = Dependent,
      members = dependentMembers,
      initiatives = initiatives,
      dependencies = foundationTeams
    )

    // Enumerate all schedules
    val allSchedules = WorkDivisionGenerator.generateAllSchedules(
      foundationTeams,
      List(dependentTeam)
    )

    // Analyze
    val report = ScheduleAnalyzer.analyze(allSchedules)
    val elapsedMs = System.currentTimeMillis() - startTime

    SweepResult(
      config = config,
      report = Some(report),
      scheduleCount = allSchedules.size,
      estimatedSchedules = estimated,
      elapsedMs = elapsedMs
    )


// --- Multi-Configuration Sweep ---

object ConfigSweep:

  /** Run all configurations sequentially and produce a sweep summary. */
  def runAll(
    configs: List[SweepConfig],
    verbose: Boolean = false,
    maxSchedules: Long = ConfigRunner.DefaultMaxSchedules
  ): SweepSummary =
    val results = configs.zipWithIndex.map { (config, idx) =>
      if verbose then
        val est = ScheduleEstimator.estimateTotalSchedules(config)
        println(f"[${idx + 1}%d/${configs.size}%d] Running: ${config.shortLabel} (est. $est%,d schedules) ...")

      val result = ConfigRunner.run(config, maxSchedules)

      if verbose then
        if result.skipped then
          println(s"  -> SKIPPED: ${result.skipReason}")
        else
          val status = if allConditionsVerified(result.report) then "ALL VERIFIED" else "SOME FAILED"
          println(f"  -> ${result.scheduleCount}%,d schedules in ${result.elapsedMs}%,d ms: $status")

      result
    }

    val allOk = results.filterNot(_.skipped).forall(r => allConditionsVerified(r.report))
    SweepSummary(results, allOk)

  def allConditionsVerified(report: Option[AnalysisReport]): Boolean =
    report.exists(r => r.optimalIncludesSynchronized && r.weightedOptimalIncludesSynchronized && r.pointwiseDominationHolds)

  // --- Summary Table Output ---

  /** Print a publication-ready summary table of all sweep results. */
  def printSummaryTable(summary: SweepSummary): Unit =
    println()
    println("=" * 120)
    println("MULTI-CONFIGURATION SWEEP SUMMARY")
    println("=" * 120)
    println()

    // Header
    val hdr = f"${"Config"}%-35s | ${"#Init"}%5s | ${"Work"}%-12s | ${"Values"}%-12s | ${"#Fnd"}%4s | ${"k"}%3s | ${"#Sched"}%10s | ${"ms"}%7s | ${"P1a"}%3s | ${"P1b"}%3s | ${"P1bW"}%4s | ${"P2"}%3s | ${"P3"}%3s | ${"P4"}%3s"
    println(hdr)
    println("-" * 152)

    for r <- summary.results do
      val c = r.config
      val label = c.shortLabel.take(35)
      val workStr = c.workPerInitiative.mkString(",")
      val valStr = if c.valuePerInitiative.nonEmpty then c.valuePerInitiative.map(v => f"$v%.0f").mkString(",") else "-"
      if r.skipped then
        println(f"${label}%-35s | ${c.numInitiatives}%5d | ${workStr}%-12s | ${valStr}%-12s | ${c.numFoundationTeams}%4d | ${c.teamSize}%3d | ${"SKIPPED"}%10s | ${r.elapsedMs}%,7d |   - |   - |    - |   - |   - |   -")
      else
        val p1a = verdictChar(r.report.exists(_.optimalAlwaysSynchronized))
        val p1b = verdictChar(r.report.exists(_.optimalIncludesSynchronized))
        val p1bw = verdictChar(r.report.exists(_.weightedOptimalIncludesSynchronized))
        val p2 = verdictChar(r.report.exists(_.syncDominatesWithinAllDistributions))
        val p3 = verdictChar(r.report.exists(_.syncDominatesOverall))
        val p4 = verdictChar(r.report.exists(_.pointwiseDominationHolds))
        println(f"${label}%-35s | ${c.numInitiatives}%5d | ${workStr}%-12s | ${valStr}%-12s | ${c.numFoundationTeams}%4d | ${c.teamSize}%3d | ${r.scheduleCount}%,10d | ${r.elapsedMs}%,7d | $p1a%3s | $p1b%3s | $p1bw%4s | $p2%3s | $p3%3s | $p4%3s")

    println("-" * 130)

    // Legend
    println()
    println("Legend:")
    println("  P1a = ALL optimal schedules are synchronized (strong)")
    println("  P1b = A synchronized schedule EXISTS at the optimum (sync is never suboptimal)")
    println("  P1bW = A synchronized schedule EXISTS at the weighted-completion-time optimum")
    println("  P2  = Sync dominates within all work-distribution classes")
    println("  P3  = Sync dominates overall (strong dominance: worst sync Cmax <= best unsync Cmax)")
    println("  P4  = Pointwise domination: for all S exists S* sync such that C_j(S*) <= C_j(S) for every job j")
    println(s"  Y = verified, N = FAILED, - = skipped")
    println()

    val ran = summary.results.filterNot(_.skipped)
    val skipped = summary.results.filter(_.skipped)
    println(s"Configurations run: ${ran.size}, skipped: ${skipped.size}")

    if summary.allVerified then
      println("RESULT: P1b verified across ALL completed configurations — synchronization is never suboptimal.")
    else
      val failedConfigs = ran.filterNot(r => allConditionsVerified(r.report))
      println(s"RESULT: ${failedConfigs.size} configuration(s) failed P1b:")
      for r <- failedConfigs do
        println(s"  - ${r.config.shortLabel}")

    if skipped.nonEmpty then
      println()
      println("Skipped configurations:")
      for r <- skipped do
        println(s"  - ${r.config.shortLabel}: ${r.skipReason}")
    println()

  /** Print a detailed report for one sweep result (delegates to ScheduleAnalyzer). */
  def printDetailedResult(result: SweepResult): Unit =
    result.report match
      case Some(report) =>
        println()
        println(s"=== Detailed Report: ${result.config.shortLabel} ===")
        ScheduleAnalyzer.printReport(report)
      case None =>
        println()
        println(s"=== ${result.config.shortLabel}: SKIPPED (${result.skipReason}) ===")

  private def verdictChar(b: Boolean): String = if b then "Y" else "N"


// --- Predefined Configuration Sets ---

object StandardConfigs:

  /** The original hardcoded configuration from Main.scala. */
  val baseline: SweepConfig = SweepConfig(
    workPerInitiative = List(2, 2),
    numFoundationTeams = 2,
    teamSize = 2,
    label = "baseline (2i, w=2,2, 2f, k=2)"
  )

  /** Symmetric work configurations. */
  def symmetric: List[SweepConfig] = List(
    baseline,
    SweepConfig(List(2,2,2),       2, 2, "3i w=2 f=2 k=2"),
    SweepConfig(List(2,2),         3, 2, "2i w=2 f=3 k=2"),
    SweepConfig(List(3,3),         2, 2, "2i w=3 f=2 k=2"),
    SweepConfig(List(2,2,2,2),     2, 2, "4i w=2 f=2 k=2"),
    SweepConfig(List(4,4),         2, 2, "2i w=4 f=2 k=2"),
    SweepConfig(List(2,2,2),       3, 2, "3i w=2 f=3 k=2"),
    SweepConfig(List(3,3,3),       2, 2, "3i w=3 f=2 k=2"),
    SweepConfig(List(2,2,2,2),     3, 2, "4i w=2 f=3 k=2"),
    SweepConfig(List(2,2,2,2,2),   2, 2, "5i w=2 f=2 k=2"),
  )

  /** Asymmetric work configurations. */
  def asymmetric: List[SweepConfig] = List(
    SweepConfig(List(3, 2),      2, 2, "asym w=3,2 f=2 k=2"),
    SweepConfig(List(2, 3),      2, 2, "asym w=2,3 f=2 k=2"),
    SweepConfig(List(2, 4),      2, 2, "asym w=2,4 f=2 k=2"),
    SweepConfig(List(3, 2, 2),   2, 2, "asym w=3,2,2 f=2 k=2"),
    SweepConfig(List(2, 3, 4),   2, 2, "asym w=2,3,4 f=2 k=2"),
    SweepConfig(List(4, 2, 2),   2, 2, "asym w=4,2,2 f=2 k=2"),
    SweepConfig(List(5, 2),      2, 2, "asym w=5,2 f=2 k=2"),
    SweepConfig(List(4, 2, 2),   3, 2, "asym w=4,2,2 f=3 k=2"),
    SweepConfig(List(2, 3),      3, 2, "asym w=2,3 f=3 k=2"),
    SweepConfig(List(3, 4, 5),   2, 3, "asym w=3,4,5 f=2 k=3"),
  )

  /** Value-weighted configurations. */
  def valueWeighted: List[SweepConfig] = List(
    SweepConfig(List(2,3,4), 2, 2, "val uniform w=2,3,4",
      valuePerInitiative = List(1,1,1)),
    SweepConfig(List(2,3,4), 2, 2, "val prop w=2,3,4 v=2,3,4",
      valuePerInitiative = List(2,3,4)),
    SweepConfig(List(2,3,4), 2, 2, "val inv w=2,3,4 v=6,4,3",
      valuePerInitiative = List(6,4,3)),
    SweepConfig(List(2,3,4), 2, 2, "val skew w=2,3,4 v=100,1,1",
      valuePerInitiative = List(100,1,1)),
    SweepConfig(List(2,3,4), 2, 2, "val skew-hard w=2,3,4 v=1,1,100",
      valuePerInitiative = List(1,1,100)),
    SweepConfig(List(3,3), 2, 2, "val asym w=3,3 v=10,1",
      valuePerInitiative = List(10,1)),
    SweepConfig(List(2,3), 3, 2, "val 3fnd w=2,3 v=5,1",
      valuePerInitiative = List(5,1)),
  )

  /** Heterogeneous-work configurations. */
  def heterogeneous: List[SweepConfig] = List(
    SweepConfig(List(4,4), 2, 2, "hetero 2i/2t w=[[4,2],[2,4]]",
      workPerTeam = List(List(4,2), List(2,4))),
    SweepConfig(List(6,3), 2, 2, "hetero 2i/2t w=[[6,2],[2,3]]",
      workPerTeam = List(List(6,2), List(2,3))),
    SweepConfig(List(3,3,3), 2, 2, "hetero 3i/2t w=[[3,2,2],[2,3,2]]",
      workPerTeam = List(List(3,2,2), List(2,3,2))),
    SweepConfig(List(3,3,3), 2, 2, "hetero 3i/2t w=[[2,3,3],[3,2,2]]",
      workPerTeam = List(List(2,3,3), List(3,2,2))),
    SweepConfig(List(4,3,2), 2, 2, "hetero 3i/2t w=[[4,2,2],[2,3,2]]",
      workPerTeam = List(List(4,2,2), List(2,3,2))),
    SweepConfig(List(3,3,3), 2, 2, "hetero 3i/2t w=[[3,3,2],[2,2,3]]",
      workPerTeam = List(List(3,3,2), List(2,2,3))),
    SweepConfig(List(3,3,3), 3, 2, "hetero 3i/3t w=diff",
      workPerTeam = List(List(3,2,2), List(2,3,2), List(2,2,3))),
    SweepConfig(List(3,2,3), 3, 2, "hetero 3i/3t w=diff2",
      workPerTeam = List(List(3,2,2), List(2,2,3), List(2,2,2))),
    SweepConfig(List(4,4), 2, 3, "hetero 2i/2t k=3 w=[[4,3],[3,4]]",
      workPerTeam = List(List(4,3), List(3,4))),
    SweepConfig(List(4,4), 3, 2, "hetero 2i/3t w=[[4,2],[2,4],[3,3]]",
      workPerTeam = List(List(4,2), List(2,4), List(3,3))),
    SweepConfig(List(3,3,3), 2, 2, "hetero+val 3i/2t v=3,1,2",
      workPerTeam = List(List(3,2,2), List(2,3,2)),
      valuePerInitiative = List(3,1,2)),
    SweepConfig(List(3,3,3), 2, 2, "hetero+val 3i/2t v=10,1,1",
      workPerTeam = List(List(3,2,2), List(2,3,2)),
      valuePerInitiative = List(10,1,1)),
  )

  /** A curated "small but thorough" set for quick validation. */
  def quick: List[SweepConfig] = List(baseline) ++ asymmetric.take(4)

  /** Full sweep: all symmetric + all asymmetric + value-weighted + heterogeneous. */
  def full: List[SweepConfig] = symmetric ++ asymmetric ++ valueWeighted ++ heterogeneous
