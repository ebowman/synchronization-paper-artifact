class MySuite extends munit.FunSuite {

  import WorkDivisionGenerator._

  // Shared test fixtures
  val initiativeA = Initiative("Initiative A", 2)
  val initiativeB = Initiative("Initiative B", 2)

  val foundationTeam1 = Team(
    name = "Foundation Team 1",
    teamType = Foundation,
    members = List(TeamMember(1), TeamMember(2)),
    initiatives = List(initiativeA, initiativeB)
  )

  val foundationTeam2 = Team(
    name = "Foundation Team 2",
    teamType = Foundation,
    members = List(TeamMember(3), TeamMember(4)),
    initiatives = List(initiativeA, initiativeB)
  )

  val dependentTeam = Team(
    name = "Dependent Team",
    teamType = Dependent,
    members = List(TeamMember(5), TeamMember(6)),
    initiatives = List(initiativeA, initiativeB),
    dependencies = List(foundationTeam1, foundationTeam2)
  )

  val foundationTeams = List(foundationTeam1, foundationTeam2)
  val dependentTeams = List(dependentTeam)

  lazy val allSchedules = generateAllSchedules(foundationTeams, dependentTeams)
  lazy val report = ScheduleAnalyzer.analyze(allSchedules)

  // --- Test 1: Enumeration completeness ---

  test("2-initiative 2-foundation-team setup produces 8 total schedules") {
    assertEquals(allSchedules.size, 8)
  }

  // --- Test 2: Classification correctness ---

  test("schedules partition into 4 synchronized and 4 unsynchronized") {
    val grouped = report.allResults.groupBy(_.classification)
    assertEquals(grouped(ScheduleClass.Synchronized).size, 4)
    assertEquals(grouped(ScheduleClass.Unsynchronized).size, 4)
  }

  test("two foundation teams with same ordering are Synchronized") {
    val synced = report.allResults.filter(_.classification == ScheduleClass.Synchronized)
    for r <- synced do
      val orderings = r.foundationOrderings
      assertEquals(orderings.distinct.size, 1,
        s"Synchronized schedule should have identical foundation orderings, got: $orderings")
  }

  test("two foundation teams with different orderings are Unsynchronized") {
    val unsynced = report.allResults.filter(_.classification == ScheduleClass.Unsynchronized)
    for r <- unsynced do
      val orderings = r.foundationOrderings
      assert(orderings.distinct.size > 1,
        s"Unsynchronized schedule should have different foundation orderings, got: $orderings")
  }

  // --- Test 3: Initiative ordering extraction ---

  test("initiativeOrder extracts correct ordering from tasks") {
    val tasks = List(
      Task(initiativeB, startTime = 0, duration = 1, List(TeamMember(1))),
      Task(initiativeA, startTime = 1, duration = 1, List(TeamMember(1)))
    )
    val ts = TeamSchedule(foundationTeam1, tasks, totalTime = 2)
    assertEquals(
      ScheduleClassifier.initiativeOrder(ts),
      List("Initiative B", "Initiative A")
    )
  }

  // --- Test 4: Makespan computation by hand ---

  test("best synchronized makespan is 3, best unsynchronized is 4") {
    // With 2 initiatives (each w=2), 2 members, composition [1,1]:
    // Synchronized [A,B]+[A,B], dependent A→B: A done at t=1, dep starts A at t=1. Makespan = 3.
    // Synchronized [A,B]+[A,B], dependent B→A: B done at t=2, dep starts B at t=2,
    //   then A at t=3. Makespan = 4. (Suboptimal dependent ordering.)
    // Unsynchronized [A,B]+[B,A]: Both A and B complete at t=2 (max across teams).
    //   Dependent can't start until t=2 regardless. Makespan = 4.
    //
    // Key result: synchronized can achieve makespan 3 (unreachable by unsynchronized).
    // The dependent team's ordering is a free variable — the BEST synchronized
    // schedule beats the BEST unsynchronized schedule.
    val syncMakespans = report.allResults
      .filter(_.classification == ScheduleClass.Synchronized)
      .map(_.makespan)
    val unsyncMakespans = report.allResults
      .filter(_.classification == ScheduleClass.Unsynchronized)
      .map(_.makespan)

    assertEquals(syncMakespans.min, 3,
      s"Best synchronized makespan should be 3, got: ${syncMakespans.min}")
    assertEquals(unsyncMakespans.min, 4,
      s"Best unsynchronized makespan should be 4, got: ${unsyncMakespans.min}")
    assert(syncMakespans.min < unsyncMakespans.min,
      "Best synchronized should strictly beat best unsynchronized")
  }

  // --- Test 5: The dominance proof ---

  test("optimal schedule includes a synchronized schedule (P1b)") {
    assert(report.optimalIncludesSynchronized,
      "A synchronized schedule should exist among the makespan-optimal schedules")
  }

  test("all optimal schedules are synchronized for baseline (P1a)") {
    assert(report.optimalAlwaysSynchronized,
      "For the baseline 2i/2f config, ALL optimal schedules should be synchronized")
  }

  test("synchronized dominates within all work distribution classes") {
    assert(report.syncDominatesWithinAllDistributions,
      "Within every work distribution class, worst sync makespan should <= best unsync makespan")
  }

  test("synchronized dominates overall (strong dominance)") {
    assert(report.syncDominatesOverall,
      s"Worst sync makespan should <= best unsync makespan. " +
      s"Sync worst: ${report.partitions.get(ScheduleClass.Synchronized).map(_.worstMakespan)}, " +
      s"Unsync best: ${report.partitions.get(ScheduleClass.Unsynchronized).map(_.bestMakespan)}")
  }

  // --- Test 6: Edge case — single foundation team is always synchronized ---

  test("single foundation team is always classified as Synchronized") {
    val singleTeamSchedules = generateAllSchedules(List(foundationTeam1), dependentTeams)
    val singleReport = ScheduleAnalyzer.analyze(singleTeamSchedules)
    assert(singleReport.allResults.forall(_.classification == ScheduleClass.Synchronized),
      "With a single foundation team, all schedules should be synchronized")
  }

  // --- Test 7: Dependent idle time is higher for unsynchronized ---

  test("unsynchronized schedules have higher average dependent idle time") {
    val syncIdle = report.partitions(ScheduleClass.Synchronized).avgDependentIdleTime
    val unsyncIdle = report.partitions(ScheduleClass.Unsynchronized).avgDependentIdleTime
    assert(unsyncIdle >= syncIdle,
      s"Unsynchronized avg idle ($unsyncIdle) should >= synchronized avg idle ($syncIdle)")
  }

  // --- Test 8: Flow time is better for synchronized ---

  test("synchronized schedules have better (lower) total flow time") {
    val syncBest = report.partitions(ScheduleClass.Synchronized).bestFlowTime
    val unsyncBest = report.partitions(ScheduleClass.Unsynchronized).bestFlowTime
    assert(syncBest <= unsyncBest,
      s"Best sync flow time ($syncBest) should <= best unsync flow time ($unsyncBest)")
  }
}
