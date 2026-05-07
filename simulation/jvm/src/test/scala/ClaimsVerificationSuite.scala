/**
 * Claims Verification Suite
 *
 * Tests that anchor the paper's quantitative claims to the code.
 * When these fail, either the paper or the code needs updating.
 *
 * See claims-registry.yaml for the full mapping of paper claims to code.
 */
class ClaimsVerificationSuite extends munit.FunSuite {

  // ================================================================
  // QUANT-CONFIG-COUNT: number of standard configurations
  // Paper (ORL Section 4) claims a specific count. Update both
  // the paper AND this constant when configs change.
  // ================================================================

  test("config counts by category") {
    assertEquals(StandardConfigs.symmetric.size, 10, "symmetric config count")
    assertEquals(StandardConfigs.asymmetric.size, 10, "asymmetric config count")
    assertEquals(StandardConfigs.valueWeighted.size, 7, "value-weighted config count")
    assertEquals(StandardConfigs.heterogeneous.size, 12, "heterogeneous config count")
    assertEquals(StandardConfigs.full.size, 39, "total config count")
  }

  // ================================================================
  // THM-1 / P4: pointwise domination on worked example
  // Paper Section 3 example: n=3, m=2, k=2, w=(2,3,4)
  // ================================================================

  test("paper worked example: n=3, m=2, k=2, w=(2,3,4) — P4 holds") {
    val config = SweepConfig(
      workPerInitiative = List(2, 3, 4),
      numFoundationTeams = 2,
      teamSize = 2,
      label = "paper-example"
    )
    val result = ConfigRunner.run(config)
    assert(!result.skipped, s"Config should not be skipped: ${result.skipReason}")
    val report = result.report.get

    // P4: pointwise domination (the main theorem)
    assert(report.pointwiseDominationHolds,
      "P4 (pointwise domination) must hold for the paper's worked example")

    // P1b: optimal includes synchronized
    assert(report.optimalIncludesSynchronized,
      "P1b must hold: a synchronized schedule exists at the optimum")

    // P1b-wct: weighted-optimal includes synchronized
    assert(report.weightedOptimalIncludesSynchronized,
      "P1b-W must hold: weighted-optimal includes a synchronized schedule")

    // Schedule count sanity (n=3, m=2, k=2 produces 46,656 schedules)
    assertEquals(report.totalSchedules, 46656,
      "schedule count for n=3, m=2, k=2, w=(2,3,4)")
  }

  // ================================================================
  // THM-1 / P4: P4 holds on every non-skipped standard config
  // This is the computational verification of the main theorem.
  // ================================================================

  test("P4 and P1b hold on all feasible standard configs") {
    // Use a conservative limit to avoid OOM in test runner.
    // CI runs the full sweep with higher limits separately.
    val maxSchedules = 120_000L
    val results = StandardConfigs.full.map(c => ConfigRunner.run(c, maxSchedules))
    val ran = results.filterNot(_.skipped)

    assert(ran.size >= 30, s"At least 30 configs should be feasible, got ${ran.size}")

    val p4Failed = ran.filter(r => !r.report.exists(_.pointwiseDominationHolds))
    assertEquals(p4Failed.map(_.config.shortLabel), Nil,
      "P4 must hold on every non-skipped config")

    val p1bFailed = ran.filter(r => !r.report.exists(_.optimalIncludesSynchronized))
    assertEquals(p1bFailed.map(_.config.shortLabel), Nil,
      "P1b must hold on every non-skipped config")
  }

  // ================================================================
  // Baseline sanity: the simplest config (n=2, m=2, k=2, w=2,2)
  // verifies all six properties including strong dominance.
  // ================================================================

  test("baseline config: all six properties hold") {
    val result = ConfigRunner.run(StandardConfigs.baseline)
    val report = result.report.get

    assertEquals(report.totalSchedules, 8)
    assert(report.optimalAlwaysSynchronized, "P1a")
    assert(report.optimalIncludesSynchronized, "P1b")
    assert(report.weightedOptimalIncludesSynchronized, "P1b-W")
    assert(report.syncDominatesWithinAllDistributions, "P2")
    assert(report.syncDominatesOverall, "P3")
    assert(report.pointwiseDominationHolds, "P4")
  }

  // ================================================================
  // Chain: P5 (makespan) holds for L=2 (CHAIN-THM-8)
  // ================================================================

  test("chain L=2: makespan domination holds (Theorem 8)") {
    val l2Configs = List(StandardChainConfigs.l2_n2_k2, StandardChainConfigs.l2_n3_k2)
    for config <- l2Configs do
      val result = ChainAnalyzer.analyze(config)
      assert(result.makespanDomHolds,
        s"P5 (makespan domination) must hold for L=2: ${config.shortLabel}")
      assert(result.flowtimeDomHolds,
        s"P6 (flowtime domination) must hold for L=2: ${config.shortLabel}")
  }

  // ================================================================
  // Chain: P4 fails for L>=3 with specific counterexamples (CHAIN-PROP-9)
  // ================================================================

  test("chain L=3: pointwise domination fails on known counterexample (Proposition 9)") {
    val result = ChainAnalyzer.analyze(StandardChainConfigs.makespan_ce_l3_n2)
    assert(!result.makespanDomHolds,
      "Makespan domination should FAIL for the L=3 counterexample config")
  }

  // ================================================================
  // Feasibility guard: infeasible configs are correctly skipped
  // ================================================================

  test("infeasible config (work < teamSize) is skipped") {
    val config = SweepConfig(
      workPerInitiative = List(1, 1),
      numFoundationTeams = 2,
      teamSize = 3,
      label = "infeasible"
    )
    val result = ConfigRunner.run(config)
    assert(result.skipped, "Config with work < teamSize should be skipped")
    assert(result.skipReason.contains("Infeasible"))
  }
}
