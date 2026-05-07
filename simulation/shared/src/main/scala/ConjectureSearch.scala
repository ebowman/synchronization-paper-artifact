/**
 * Systematic search for counterexamples to the Chain Dominance Conjecture.
 *
 * The conjecture states: For any L-stage chain with preemptive priority,
 * there exists a synchronized (permutation) schedule that minimises C_max
 * and separately minimises Σ v_j C_j^L.
 *
 * We search across work profiles to find when the conjecture fails.
 */
object ConjectureSearch:

  case class SearchResult(
    config: ChainConfig,
    p5Holds: Boolean,
    p6Holds: Boolean,
    bestSyncMakespan: Double,
    bestUnsyncMakespan: Double,
    makespanGap: Double,       // sync - unsync (positive = conjecture fails)
    bestSyncFlowtime: Double,
    bestUnsyncFlowtime: Double,
    flowtimeGap: Double
  )

  def searchL3n2(kValues: List[Int], workRange: Range): List[SearchResult] =
    var results = List.empty[SearchResult]
    var ceCount = 0

    for {
      k <- kValues
      w00 <- workRange
      w01 <- workRange
      w10 <- workRange
      w11 <- workRange
      w20 <- workRange
      w21 <- workRange
    } {
      val config = ChainConfig(
        numStages = 3,
        workPerStage = List(List(w00, w01), List(w10, w11), List(w20, w21)),
        workersPerStage = List(k, k, k),
        label = s"k=$k w=[($w00,$w01),($w10,$w11),($w20,$w21)]"
      )

      val result = analyzeQuick(config)
      if (!result.p5Holds || !result.p6Holds) {
        results = result :: results
        ceCount += 1
      }
    }

    results.reverse

  def analyzeQuick(config: ChainConfig): SearchResult =
    val n = config.numJobs
    val L = config.numStages
    val perms = (0 until n).toList.permutations.toList.map(_.toIndexedSeq)

    // Synchronized schedules
    val syncResults = perms.map { perm =>
      val orderings = IndexedSeq.fill(L)(perm)
      val comps = PreemptivePriorityScheduler.scheduleChain(config, orderings)
      val finalComps = comps.last
      (finalComps.values.max, finalComps.values.sum)
    }

    // All orderings
    def cartProd[T](lists: List[List[T]]): List[List[T]] =
      lists.foldRight(List(List.empty[T])) { (cur, acc) =>
        for { e <- cur; c <- acc } yield e :: c
      }

    val allResults = cartProd(List.fill(L)(perms)).map { ordering =>
      val comps = PreemptivePriorityScheduler.scheduleChain(config, ordering.map(_.toIndexedSeq).toIndexedSeq)
      val finalComps = comps.last
      (finalComps.values.max, finalComps.values.sum)
    }

    val bestSyncMakespan = syncResults.map(_._1).min
    val bestSyncFlowtime = syncResults.map(_._2).min
    val bestAllMakespan = allResults.map(_._1).min
    val bestAllFlowtime = allResults.map(_._2).min

    SearchResult(
      config = config,
      p5Holds = bestSyncMakespan <= bestAllMakespan + 1e-9,
      p6Holds = bestSyncFlowtime <= bestAllFlowtime + 1e-9,
      bestSyncMakespan = bestSyncMakespan,
      bestUnsyncMakespan = bestAllMakespan,
      makespanGap = bestSyncMakespan - bestAllMakespan,
      bestSyncFlowtime = bestSyncFlowtime,
      bestUnsyncFlowtime = bestAllFlowtime,
      flowtimeGap = bestSyncFlowtime - bestAllFlowtime
    )

  def main(args: Array[String]): Unit =
    println("Systematic Search for Chain Conjecture Counterexamples")
    println("=" * 80)

    // Search L=3, n=2 with work values 1-6
    for (k <- List(2, 3)) {
      println(s"\n--- k=$k, L=3, n=2, work range 1..6 ---")
      val ces = searchL3n2(List(k), 1 to 6)
      println(s"Found ${ces.size} counterexamples out of ${math.pow(6, 6).toInt} configs")

      if (ces.nonEmpty) {
        // Show largest gap
        val byMakespanGap = ces.sortBy(-_.makespanGap)
        println(s"\nTop 5 makespan counterexamples (largest gap):")
        for (r <- byMakespanGap.take(5)) {
          println(f"  ${r.config.shortLabel}%-45s gap=${r.makespanGap}%.3f  sync=${r.bestSyncMakespan}%.2f  best=${r.bestUnsyncMakespan}%.2f")
        }

        val byFlowtimeGap = ces.sortBy(-_.flowtimeGap)
        println(s"\nTop 5 flowtime counterexamples (largest gap):")
        for (r <- byFlowtimeGap.take(5)) {
          println(f"  ${r.config.shortLabel}%-45s gap=${r.flowtimeGap}%.3f  sync=${r.bestSyncFlowtime}%.2f  best=${r.bestUnsyncFlowtime}%.2f")
        }

        // Characterize: what do counterexamples have in common?
        println(s"\nCharacterization:")
        val makespanCEs = ces.filter(!_.p5Holds)
        val flowtimeCEs = ces.filter(!_.p6Holds)
        println(s"  P5 (makespan) failures: ${makespanCEs.size}")
        println(s"  P6 (flowtime) failures: ${flowtimeCEs.size}")

        // Check: do all CEs have inverted work profiles?
        val inverted = makespanCEs.count { r =>
          val w = r.config.workPerStage
          // Check if work is "inverted" between stages 0 and 1
          val w0ratio = w(0)(0).toDouble / w(0)(1)
          val w1ratio = w(1)(0).toDouble / w(1)(1)
          (w0ratio < 1 && w1ratio > 1) || (w0ratio > 1 && w1ratio < 1)
        }
        println(s"  P5 CEs with work inversion (stages 0-1): $inverted of ${makespanCEs.size}")
      }
    }
