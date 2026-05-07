/**
 * Investigation of P1 failure for w=3,2,2 f=2 k=2.
 *
 * Questions:
 * 1. Is the P1 failure genuine (unsynchronized schedules can truly be optimal)?
 * 2. Or is there a bug in initiativeOrder when compositions create tied min-start-times?
 */
class P1InvestigationSuite extends munit.FunSuite {

  import WorkDivisionGenerator._

  // ============================================================
  // Part 1: Run w=3,2,2 and inspect optimal schedules
  // ============================================================

  val config322 = SweepConfig(
    workPerInitiative = List(3, 2, 2),
    numFoundationTeams = 2,
    teamSize = 2,
    label = "investigation w=3,2,2 f=2 k=2"
  )

  // Build teams manually so we can inspect them
  val initA = Initiative("Initiative A", 3)
  val initB = Initiative("Initiative B", 2)
  val initC = Initiative("Initiative C", 2)
  val initiatives = List(initA, initB, initC)

  val ft1 = Team("Foundation Team 1", Foundation,
    List(TeamMember(1), TeamMember(2)), initiatives)
  val ft2 = Team("Foundation Team 2", Foundation,
    List(TeamMember(3), TeamMember(4)), initiatives)
  val dt = Team("Dependent Team", Dependent,
    List(TeamMember(5), TeamMember(6)), initiatives,
    dependencies = List(ft1, ft2))

  lazy val allSchedules = generateAllSchedules(List(ft1, ft2), List(dt))
  lazy val report = ScheduleAnalyzer.analyze(allSchedules)

  test("w=3,2,2: enumerate and find optimal schedules") {
    val globalOptimal = report.allResults.map(_.makespan).min
    val optimalSchedules = report.allResults.filter(_.makespan == globalOptimal)

    println(s"\n${"=" * 80}")
    println(s"INVESTIGATION: w=3,2,2 f=2 k=2")
    println(s"${"=" * 80}")
    println(s"Total schedules: ${report.allResults.size}")
    println(s"Global optimal makespan: $globalOptimal")
    println(s"Number of optimal schedules: ${optimalSchedules.size}")
    println()

    // Show classification breakdown of optimal schedules
    val byClass = optimalSchedules.groupBy(_.classification)
    for (cls, group) <- byClass do
      println(s"Optimal $cls: ${group.size} schedule(s)")
    println()

    // Show the P1 verdict
    println(s"P1 (optimal is always synchronized): ${report.optimalAlwaysSynchronized}")
    println()

    // Print details of ALL optimal schedules
    for (r, idx) <- optimalSchedules.zipWithIndex do
      println(s"--- Optimal Schedule #${idx + 1} (${r.classification}) ---")
      println(s"  Makespan: ${r.makespan}")
      println(s"  Foundation orderings: ${r.foundationOrderings.map(_.mkString("->")).mkString(" | ")}")
      println(s"  Work distribution key: ${r.workDistributionKey}")
      println()

      // Print per-team task details
      for ts <- r.combined do
        println(s"  ${ts.team.name} (${ts.team.teamType}, totalTime=${ts.totalTime}):")
        val tasksByMember = ts.tasks.groupBy(_.assignedTeamMembers.head)
        for (member, tasks) <- tasksByMember.toList.sortBy(_._1.id) do
          val taskStr = tasks.sortBy(_.startTime).map { t =>
            s"${t.initiative.name}[${t.startTime}-${t.startTime + t.duration}]"
          }.mkString(", ")
          println(s"    Member ${member.id}: $taskStr")
      println()

    // Also print the best synchronized and best unsynchronized for comparison
    val syncResults = report.allResults.filter(_.classification == ScheduleClass.Synchronized)
    val unsyncResults = report.allResults.filter(_.classification == ScheduleClass.Unsynchronized)

    if syncResults.nonEmpty then
      println(s"Best synchronized makespan: ${syncResults.map(_.makespan).min}")
    if unsyncResults.nonEmpty then
      println(s"Best unsynchronized makespan: ${unsyncResults.map(_.makespan).min}")
    println()
  }

  // ============================================================
  // Part 2: Check for tie-breaking ambiguity in initiativeOrder
  // ============================================================

  test("initiativeOrder: tied min-start-times produce ambiguous ordering") {
    // Construct a scenario where two initiatives start at the same time
    // on different members.
    //
    // If initiative order is A, B, C with A=[2,1], B=[1,1], C=[1,1]:
    //   Member 1: A(0-2), B(2-3), C(3-4)
    //   Member 2: A(0-1), B(1-2), C(2-3)
    //   Min starts: A=0, B=1, C=2 -> no ties
    //
    // But what about A=[1,2], B=[1,1], C=[1,1]:
    //   Member 1: A(0-1), B(1-2), C(2-3)
    //   Member 2: A(0-2), B(2-3), C(3-4)
    //   Min starts: A=0, B=1, C=2 -> no ties
    //
    // Can we get ties? With 3 initiatives, the building algorithm processes
    // them sequentially per initiative, so each initiative starts after
    // the previous one on every member. The min start of initiative i+1
    // is always >= min start of initiative i. But can they be EQUAL?
    //
    // Consider order A, B with A=[2,1], B=[1,1]:
    //   Member 1: A(0-2), B(2-3)
    //   Member 2: A(0-1), B(1-2)
    //   Min starts: A=0, B=1 -> no tie
    //
    // For a tie to happen, one member would need to finish initiative i
    // at time T, and another member would need to have already started
    // initiative i+1 at time T' <= T. But the algorithm processes ALL
    // members for initiative i before moving to initiative i+1. So
    // member j cannot start initiative i+1 before ALL members have been
    // assigned initiative i's work. Member j starts initiative i+1 at
    // its own currentTime after initiative i, which is at least 1 (since
    // each composition part >= 1).
    //
    // Actually, let's check: could min_start(initiative_i+1) == min_start(initiative_i)?
    // Min start of initiative 0 is always 0 (for all members, since no work precedes it).
    // Min start of initiative 1: the member with the smallest work portion for initiative 0.
    // If initiative 0 has composition [1, ...], then at least one member finishes initiative 0
    // at time 1, so min start of initiative 1 is 1. Never 0.
    //
    // So within a single team, initiativeOrder cannot have ties between
    // consecutive initiatives. But can non-consecutive initiatives tie?
    // No - start times are monotonically increasing per member.
    //
    // THEREFORE: within a single team, initiativeOrder always produces
    // a well-defined total order. No ambiguity.

    // Verify this claim empirically: check all schedules in the w=3,2,2 config
    var tieCount = 0
    for combined <- allSchedules do
      val foundationSchedules = combined.filter(_.team.teamType == Foundation)
      for ts <- foundationSchedules do
        val startTimes = ts.tasks.groupBy(_.initiative.name)
          .view.mapValues(_.map(_.startTime).min).toMap
        val values = startTimes.values.toList
        if values.size != values.distinct.size then
          tieCount += 1
          println(s"TIE FOUND in ${ts.team.name}: $startTimes")

    println(s"\nTied min-start-time count across all schedules: $tieCount")
    assertEquals(tieCount, 0, "No ties expected in min-start-times within a single team")
  }

  // ============================================================
  // Part 3: Check if the unsynchronized optimal is genuinely better
  // ============================================================

  test("w=3,2,2: verify by manual construction whether unsync can be optimal") {
    // Let's find all optimal unsynchronized schedules and check if there
    // exists a synchronized schedule with the SAME or better makespan.
    val globalOptimal = report.allResults.map(_.makespan).min
    val optUnsync = report.allResults.filter(r =>
      r.makespan == globalOptimal && r.classification == ScheduleClass.Unsynchronized)
    val optSync = report.allResults.filter(r =>
      r.makespan == globalOptimal && r.classification == ScheduleClass.Synchronized)

    println(s"\n${"=" * 80}")
    println(s"DIAGNOSIS: Is the P1 failure genuine?")
    println(s"${"=" * 80}")
    println(s"Global optimal makespan: $globalOptimal")
    println(s"Optimal synchronized schedules: ${optSync.size}")
    println(s"Optimal unsynchronized schedules: ${optUnsync.size}")

    if optSync.nonEmpty && optUnsync.nonEmpty then
      println("\nBoth sync and unsync achieve optimal -> P1 is TECHNICALLY false")
      println("but this means unsync TIES sync, not that unsync BEATS sync.")
      println("The question is: does any unsync schedule STRICTLY beat all sync schedules?")

      val bestSync = report.allResults
        .filter(_.classification == ScheduleClass.Synchronized)
        .map(_.makespan).min
      val bestUnsync = report.allResults
        .filter(_.classification == ScheduleClass.Unsynchronized)
        .map(_.makespan).min

      println(s"\nBest sync makespan: $bestSync")
      println(s"Best unsync makespan: $bestUnsync")

      if bestUnsync < bestSync then
        println("GENUINE: Unsynchronized STRICTLY beats synchronized!")
      else if bestUnsync == bestSync then
        println("TIE: Unsynchronized ties synchronized at the optimum.")
        println("P1 fails because optimal set INCLUDES unsynchronized schedules.")
        println("This is a GENUINE result but with a weak interpretation:")
        println("  Synchronized is ALWAYS among the optimal, but not EXCLUSIVELY optimal.")
      else
        println("BUG: Unsync is worse but somehow classified as optimal?!")

    else if optSync.isEmpty then
      println("\nNO synchronized schedule achieves optimal -> GENUINE P1 failure")
      println("Unsynchronized truly beats synchronized.")
    else
      println("\nAll optimal schedules are synchronized -> P1 should pass")
      println("If P1 failed, there may be a bug in the report logic.")
  }

  // ============================================================
  // Part 4: Compare with w=2,3,4 (which passes P1)
  // ============================================================

  test("w=2,3,4: confirm P1 passes") {
    val result234 = ConfigRunner.run(SweepConfig(
      workPerInitiative = List(2, 3, 4),
      numFoundationTeams = 2,
      teamSize = 2,
      label = "comparison w=2,3,4 f=2 k=2"
    ))

    val rpt = result234.report.get
    println(s"\n${"=" * 80}")
    println(s"COMPARISON: w=2,3,4 f=2 k=2")
    println(s"${"=" * 80}")
    println(s"Total schedules: ${rpt.allResults.size}")
    println(s"P1 (optimal always synchronized): ${rpt.optimalAlwaysSynchronized}")

    val globalOpt = rpt.allResults.map(_.makespan).min
    val optByClass = rpt.allResults.filter(_.makespan == globalOpt).groupBy(_.classification)
    for (cls, group) <- optByClass do
      println(s"  Optimal $cls: ${group.size}")

    assert(rpt.optimalAlwaysSynchronized, "w=2,3,4 should have P1 verified")
  }

  // ============================================================
  // Part 5: Deep dive - print the mechanism for w=3,2,2
  // ============================================================

  test("w=3,2,2: explain WHY unsynchronized can tie") {
    val globalOptimal = report.allResults.map(_.makespan).min
    val optUnsync = report.allResults.filter(r =>
      r.makespan == globalOptimal && r.classification == ScheduleClass.Unsynchronized)

    if optUnsync.nonEmpty then
      println(s"\n${"=" * 80}")
      println("MECHANISM: Why unsynchronized ties optimal for w=3,2,2")
      println(s"${"=" * 80}")

      val example = optUnsync.head
      println(s"Example unsynchronized optimal (makespan=${example.makespan}):")

      for ts <- example.combined do
        val ordering = ScheduleClassifier.initiativeOrder(ts)
        println(s"\n  ${ts.team.name} (${ts.team.teamType}):")
        println(s"  Initiative order: ${ordering.mkString(" -> ")}")
        val tasksByMember = ts.tasks.groupBy(_.assignedTeamMembers.head)
        for (member, tasks) <- tasksByMember.toList.sortBy(_._1.id) do
          val taskStr = tasks.sortBy(_.startTime).map { t =>
            s"${t.initiative.name.last}[${t.startTime}-${t.startTime + t.duration}](w=${t.duration})"
          }.mkString(", ")
          println(s"    Member ${member.id}: $taskStr")

      // Show completion times per initiative across foundation teams
      val foundationSchedules = example.combined.filter(_.team.teamType == Foundation)
      val completionTimes = WorkDivisionGenerator.computeInitiativeCompletionTimes(foundationSchedules)
      println(s"\n  Foundation completion times (max across teams per initiative):")
      for (init, time) <- completionTimes.toList.sortBy(_._2) do
        println(s"    ${init.name}: $time")

      println(s"\n  Key insight: With asymmetric work (w=3 vs w=2), different teams")
      println(s"  can process the 'heavy' initiative at different positions in the order")
      println(s"  and STILL achieve the same completion profile if the compositions")
      println(s"  compensate for the ordering difference.")
    else
      println("\nNo unsynchronized optimal schedules found - P1 should pass.")
      println("If P1 is reported as failed, check the report logic.")
  }
}
