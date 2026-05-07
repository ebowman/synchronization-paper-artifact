/**
 * Stress test of Concordant Flowtime Dominance conjecture for n=3 jobs.
 *
 * Tests:
 *   1. L=3, n=3, k=2, work 1..5 (concordant configs only)
 *   2. L=4, n=3, k=2, work 1..3 (concordant configs only)
 *
 * Efficient generation: only iterate over concordant work profiles by
 * fixing job ordering w_l(0) <= w_l(1) <= w_l(2) at every stage.
 * This guarantees concordance and covers all concordant configs up to
 * job relabeling.
 */
object N3ConcordantStress:

  /** Generate all non-decreasing triples (a,b,c) with a <= b <= c in [lo, hi]. */
  private def concordantTriples(lo: Int, hi: Int): IndexedSeq[(Int, Int, Int)] =
    val buf = scala.collection.mutable.ArrayBuffer.empty[(Int, Int, Int)]
    for {
      a <- lo to hi
      b <- a to hi
      c <- b to hi
    } buf += ((a, b, c))
    buf.toIndexedSeq

  def main(args: Array[String]): Unit =
    println("=" * 80)
    println("CONCORDANT FLOWTIME DOMINANCE CONJECTURE — n=3 STRESS TEST")
    println("=" * 80)
    println()

    // ---- Test 1: L=3, n=3, k=2, work 1..5 ----
    runTest(
      label = "L=3, n=3, k=2, work 1..5",
      numStages = 3,
      k = 2,
      workLo = 1,
      workHi = 5
    )

    println()

    // ---- Test 2: L=4, n=3, k=2, work 1..3 ----
    runTest(
      label = "L=4, n=3, k=2, work 1..3",
      numStages = 4,
      k = 2,
      workLo = 1,
      workHi = 3
    )

    println()
    println("Done.")

  private def runTest(
    label: String,
    numStages: Int,
    k: Int,
    workLo: Int,
    workHi: Int
  ): Unit =
    println(s"--- $label ---")

    val triples = concordantTriples(workLo, workHi)
    val numTriples = triples.size
    val totalConfigs = math.pow(numTriples, numStages).toLong
    println(f"  Non-decreasing triples in [$workLo,$workHi]: $numTriples")
    println(f"  Total concordant configs (triples^$numStages): $totalConfigs%,d")

    val startTime = System.currentTimeMillis()

    var tested = 0L
    var p5Fails = 0L
    var p6Fails = 0L
    val reportInterval = 50000L

    // Cartesian product of triples across stages via recursive iteration
    def iterate(stage: Int, acc: List[List[Int]]): Unit =
      if stage == numStages then
        // acc is reversed list of work-per-stage rows
        val workPerStage = acc.reverse
        val config = ChainConfig(
          numStages,
          workPerStage,
          List.fill(numStages)(k),
          ""
        )

        // Verify concordance (sanity check on first few)
        if tested < 10 then
          assert(ConcordantTest.isConcordant(config),
            s"Generated config is not concordant: $workPerStage")

        val r = ConjectureSearch.analyzeQuick(config)
        if !r.p5Holds then
          p5Fails += 1
          if p5Fails <= 5 then
            println(s"    P5 FAIL: work=$workPerStage, syncMakespan=${r.bestSyncMakespan}, unsyncMakespan=${r.bestUnsyncMakespan}, gap=${r.makespanGap}")
        if !r.p6Holds then
          p6Fails += 1
          if p6Fails <= 5 then
            println(s"    P6 FAIL: work=$workPerStage, syncFlowtime=${r.bestSyncFlowtime}, unsyncFlowtime=${r.bestUnsyncFlowtime}, gap=${r.flowtimeGap}")

        tested += 1
        if tested % reportInterval == 0 then
          val elapsed = (System.currentTimeMillis() - startTime) / 1000.0
          val rate = tested / elapsed
          val remaining = (totalConfigs - tested) / rate
          println(f"    Progress: $tested%,d / $totalConfigs%,d  (${100.0 * tested / totalConfigs}%.1f%%)  elapsed=${elapsed}%.0fs  ETA=${remaining}%.0fs  P5fails=$p5Fails  P6fails=$p6Fails")
      else
        for t <- triples do
          iterate(stage + 1, List(t._1, t._2, t._3) :: acc)

    iterate(0, Nil)

    val elapsed = (System.currentTimeMillis() - startTime) / 1000.0
    println()
    println(f"  Results for $label:")
    println(f"    Concordant configs tested: $tested%,d")
    println(f"    P5 (makespan) failures:    $p5Fails")
    println(f"    P6 (flowtime) failures:    $p6Fails")
    println(f"    Elapsed: ${elapsed}%.1f seconds")
    if p5Fails == 0 && p6Fails == 0 then
      println(f"    CONJECTURE HOLDS for all $tested%,d concordant configs.")
    else
      println(f"    *** CONJECTURE VIOLATED ***")
