/**
 * Restricted Conjectures for L-Stage Chain Scheduling
 *
 * The general conjecture is FALSE: for L>=3, synchronized schedules do NOT
 * always achieve optimal makespan or flowtime. But restricted versions may hold.
 *
 * Tests four hypotheses:
 *   H1: Monotone work profiles — w_ℓ(A) >= w_ℓ(B) for ALL ℓ => sync dominance?
 *   H2: Proportional work — w_ℓ(j) = α_ℓ · w_j => sync dominance?
 *   H3: Same-work stages — identical work profile at every stage => sync dominance?
 *   H4: Bounded ratio — worst-case ratio of best sync makespan to best overall makespan?
 */

object RestrictedConjectures:

  // ---- Helpers ----

  /** Generate all permutations of job indices. */
  private def perms(n: Int): List[IndexedSeq[Int]] =
    (0 until n).toList.permutations.toList.map(_.toIndexedSeq)

  /** Cartesian product of lists. */
  private def cartesianProduct[T](lists: List[List[T]]): List[List[T]] =
    lists.foldRight(List(List.empty[T])) { (cur, acc) =>
      for { elem <- cur; comb <- acc } yield elem :: comb
    }

  /**
   * For a config, compute (bestSyncMakespan, bestOverallMakespan, bestSyncFlowtime, bestOverallFlowtime).
   */
  private def evaluateConfig(config: ChainConfig): (Double, Double, Double, Double) =
    val n = config.numJobs
    val L = config.numStages
    val allPerms = perms(n)

    // Sync schedules: same ordering at every stage
    val syncResults = allPerms.map { perm =>
      val orderings = IndexedSeq.fill(L)(perm)
      val completions = PreemptivePriorityScheduler.scheduleChain(config, orderings)
      val finalStage = completions.last
      val makespan = finalStage.values.max
      val flowtime = finalStage.values.sum
      (makespan, flowtime)
    }
    val bestSyncMakespan = syncResults.map(_._1).min
    val bestSyncFlowtime = syncResults.map(_._2).min

    // All orderings: cartesian product across stages
    val allOrderings = cartesianProduct(List.fill(L)(allPerms)).map(_.toIndexedSeq)
    val allResults = allOrderings.map { orderings =>
      val completions = PreemptivePriorityScheduler.scheduleChain(config, orderings.map(_.toIndexedSeq))
      val finalStage = completions.last
      val makespan = finalStage.values.max
      val flowtime = finalStage.values.sum
      (makespan, flowtime)
    }
    val bestOverallMakespan = allResults.map(_._1).min
    val bestOverallFlowtime = allResults.map(_._2).min

    (bestSyncMakespan, bestOverallMakespan, bestSyncFlowtime, bestOverallFlowtime)

  /**
   * Check pointwise domination: for every schedule, does some sync schedule dominate it?
   */
  private def checkPointwiseDomination(config: ChainConfig): Boolean =
    val n = config.numJobs
    val L = config.numStages
    val allPerms = perms(n)

    val syncCompletions = allPerms.map { perm =>
      val orderings = IndexedSeq.fill(L)(perm)
      PreemptivePriorityScheduler.scheduleChain(config, orderings).last
    }

    val allOrderings = cartesianProduct(List.fill(L)(allPerms)).map(_.toIndexedSeq)
    allOrderings.forall { orderings =>
      val completions = PreemptivePriorityScheduler.scheduleChain(config, orderings.map(_.toIndexedSeq)).last
      syncCompletions.exists { syncFinal =>
        (0 until n).forall(j => syncFinal(j) <= completions(j) + 1e-9)
      }
    }

  // ---- Config generators ----

  /** H1: Monotone work profiles. Job i has w_ℓ(i) such that the relative ordering is the same at every stage. */
  private def generateMonotoneConfigs(L: Int, n: Int, k: Int, maxWork: Int): List[ChainConfig] =
    val workRange = (1 to maxWork).toList
    // Generate all possible work vectors of length n from workRange
    val allWorkVectors = cartesianProduct(List.fill(n)(workRange))

    // For monotone: at every stage, the ordering of jobs by work must be the same.
    // We pick a base ordering (sorted ascending), then generate stage work vectors
    // that preserve that ordering.
    // Simpler: generate L work vectors, keep only those where all stages have the same
    // pairwise ordering for every pair (i,j).

    val stageWorkCombos = cartesianProduct(List.fill(L)(allWorkVectors))

    val monotoneConfigs = stageWorkCombos.filter { stageWorks =>
      // Check: for every pair (i,j), the sign of w_ℓ(i) - w_ℓ(j) is the same across all stages
      val pairs = for (i <- 0 until n; j <- i + 1 until n) yield (i, j)
      pairs.forall { case (i, j) =>
        val signs = stageWorks.map { w => (w(i) - w(j)).sign }
        signs.forall(_ == signs.head)
      }
    }

    monotoneConfigs.map { stageWorks =>
      ChainConfig(
        numStages = L,
        workPerStage = stageWorks,
        workersPerStage = List.fill(L)(k),
        label = s"monotone L=$L n=$n k=$k w=${stageWorks.map(_.mkString(",")).mkString("|")}"
      )
    }

  /** H2: Proportional work. w_ℓ(j) = α_ℓ · w_j. */
  private def generateProportionalConfigs(L: Int, n: Int, k: Int, maxWork: Int): List[ChainConfig] =
    val workRange = (1 to maxWork).toList
    val baseVectors = cartesianProduct(List.fill(n)(workRange))
    val scaleFactors = (1 to maxWork).toList
    val scaleCombos = cartesianProduct(List.fill(L)(scaleFactors))

    for {
      base <- baseVectors
      scales <- scaleCombos
    } yield {
      val stageWorks = scales.map { alpha =>
        base.map(_ * alpha)
      }
      ChainConfig(
        numStages = L,
        workPerStage = stageWorks,
        workersPerStage = List.fill(L)(k),
        label = s"proportional L=$L n=$n k=$k base=${base.mkString(",")} scales=${scales.mkString(",")}"
      )
    }

  /** H3: Same-work stages. Every stage has identical work vector. */
  private def generateSameWorkConfigs(L: Int, n: Int, k: Int, maxWork: Int): List[ChainConfig] =
    val workRange = (1 to maxWork).toList
    val allWorkVectors = cartesianProduct(List.fill(n)(workRange))

    allWorkVectors.map { w =>
      ChainConfig(
        numStages = L,
        workPerStage = List.fill(L)(w),
        workersPerStage = List.fill(L)(k),
        label = s"same-work L=$L n=$n k=$k w=${w.mkString(",")}"
      )
    }

  /** General configs for H4 bounded ratio analysis. */
  private def generateAllConfigs(L: Int, n: Int, k: Int, maxWork: Int): List[ChainConfig] =
    val workRange = (1 to maxWork).toList
    val allWorkVectors = cartesianProduct(List.fill(n)(workRange))
    val stageWorkCombos = cartesianProduct(List.fill(L)(allWorkVectors))

    stageWorkCombos.map { stageWorks =>
      ChainConfig(
        numStages = L,
        workPerStage = stageWorks,
        workersPerStage = List.fill(L)(k),
        label = s"general L=$L n=$n k=$k"
      )
    }

  // ---- Test runners ----

  private def testHypothesis(
    name: String,
    configs: List[ChainConfig],
    checkMakespan: Boolean = true,
    checkFlowtime: Boolean = true,
    checkPointwise: Boolean = true
  ): Unit =
    println(s"\n${"=" * 80}")
    println(s"  $name")
    println(s"${"=" * 80}")
    println(s"  Testing ${configs.size} configurations...")

    var makespanFails = 0
    var flowtimeFails = 0
    var pointwiseFails = 0
    var worstMakespanRatio = 1.0
    var worstFlowtimeRatio = 1.0
    var worstMakespanConfig: Option[ChainConfig] = None
    var worstFlowtimeConfig: Option[ChainConfig] = None

    for (config <- configs) {
      val (bestSyncMs, bestAllMs, bestSyncFt, bestAllFt) = evaluateConfig(config)

      if (checkMakespan && bestSyncMs > bestAllMs + 1e-9) {
        makespanFails += 1
        val ratio = bestSyncMs / bestAllMs
        if (ratio > worstMakespanRatio) {
          worstMakespanRatio = ratio
          worstMakespanConfig = Some(config)
        }
      }
      if (checkFlowtime && bestSyncFt > bestAllFt + 1e-9) {
        flowtimeFails += 1
        val ratio = bestSyncFt / bestAllFt
        if (ratio > worstFlowtimeRatio) {
          worstFlowtimeRatio = ratio
          worstFlowtimeConfig = Some(config)
        }
      }
      if (checkPointwise && !checkPointwiseDomination(config)) {
        pointwiseFails += 1
      }
    }

    println(s"\n  Results (${configs.size} configs):")
    if (checkPointwise)
      println(s"    Pointwise domination: ${if pointwiseFails == 0 then "HOLDS" else s"FAILS ($pointwiseFails counterexamples)"}")
    if (checkMakespan) {
      println(s"    Makespan dominance:   ${if makespanFails == 0 then "HOLDS" else s"FAILS ($makespanFails counterexamples)"}")
      if (makespanFails > 0) {
        println(f"      Worst ratio: $worstMakespanRatio%.4f")
        worstMakespanConfig.foreach(c => println(s"      Worst config: ${c.label}"))
      }
    }
    if (checkFlowtime) {
      println(s"    Flowtime dominance:   ${if flowtimeFails == 0 then "HOLDS" else s"FAILS ($flowtimeFails counterexamples)"}")
      if (flowtimeFails > 0) {
        println(f"      Worst ratio: $worstFlowtimeRatio%.4f")
        worstFlowtimeConfig.foreach(c => println(s"      Worst config: ${c.label}"))
      }
    }

  private def testBoundedRatio(L: Int, n: Int, k: Int, maxWork: Int): Unit =
    println(s"\n${"=" * 80}")
    println(s"  H4: BOUNDED RATIO ANALYSIS (L=$L, n=$n, k=$k, work 1-$maxWork)")
    println(s"${"=" * 80}")

    val configs = generateAllConfigs(L, n, k, maxWork)
    println(s"  Testing ${configs.size} configurations...")

    var worstMakespanRatio = 1.0
    var worstFlowtimeRatio = 1.0
    var worstMsConfig: Option[(ChainConfig, Double, Double)] = None
    var worstFtConfig: Option[(ChainConfig, Double, Double)] = None
    var makespanGaps = 0
    var flowtimeGaps = 0

    for (config <- configs) {
      val (bestSyncMs, bestAllMs, bestSyncFt, bestAllFt) = evaluateConfig(config)

      val msRatio = if bestAllMs > 1e-9 then bestSyncMs / bestAllMs else 1.0
      val ftRatio = if bestAllFt > 1e-9 then bestSyncFt / bestAllFt else 1.0

      if (msRatio > 1.0 + 1e-9) makespanGaps += 1
      if (ftRatio > 1.0 + 1e-9) flowtimeGaps += 1

      if (msRatio > worstMakespanRatio) {
        worstMakespanRatio = msRatio
        worstMsConfig = Some((config, bestSyncMs, bestAllMs))
      }
      if (ftRatio > worstFlowtimeRatio) {
        worstFlowtimeRatio = ftRatio
        worstFtConfig = Some((config, bestSyncFt, bestAllFt))
      }
    }

    println(s"\n  Results (${configs.size} configs):")
    println(f"    Makespan: $makespanGaps configs where sync is suboptimal")
    println(f"    Worst makespan ratio (sync/optimal): $worstMakespanRatio%.6f")
    worstMsConfig.foreach { case (c, syncMs, allMs) =>
      println(f"      Best sync=$syncMs%.2f, best overall=$allMs%.2f")
      println(s"      Config: ${c.workPerStage.map(_.mkString("[",",","]")).mkString(" | ")}")
    }
    println(f"    Flowtime: $flowtimeGaps configs where sync is suboptimal")
    println(f"    Worst flowtime ratio (sync/optimal): $worstFlowtimeRatio%.6f")
    worstFtConfig.foreach { case (c, syncFt, allFt) =>
      println(f"      Best sync=$syncFt%.2f, best overall=$allFt%.2f")
      println(s"      Config: ${c.workPerStage.map(_.mkString("[",",","]")).mkString(" | ")}")
    }

  // ---- Main ----

  def main(args: Array[String]): Unit =
    println("RESTRICTED CONJECTURES: L-STAGE CHAIN SCHEDULING")
    println("Testing whether sync dominance holds under structural restrictions")
    println("Model: preemptive priority, all k workers on highest-priority job")

    val startTime = System.currentTimeMillis()

    // ---- H1: Monotone work profiles ----
    // L=3, n=2, k=2, work 1-6 => monotone subset
    val monotone_3_2 = generateMonotoneConfigs(3, 2, 2, 6)
    testHypothesis("H1: MONOTONE WORK PROFILES (L=3, n=2, k=2, work 1-6)", monotone_3_2)

    // L=3, n=3, k=2, work 1-3 (smaller range to keep combinatorics tractable)
    val monotone_3_3 = generateMonotoneConfigs(3, 3, 2, 3)
    testHypothesis("H1: MONOTONE WORK PROFILES (L=3, n=3, k=2, work 1-3)", monotone_3_3)

    // ---- H2: Proportional work ----
    val proportional_3_2 = generateProportionalConfigs(3, 2, 2, 6)
    testHypothesis("H2: PROPORTIONAL WORK (L=3, n=2, k=2, work/scales 1-6)", proportional_3_2)

    val proportional_3_3 = generateProportionalConfigs(3, 3, 2, 3)
    testHypothesis("H2: PROPORTIONAL WORK (L=3, n=3, k=2, work/scales 1-3)", proportional_3_3)

    // ---- H3: Same-work stages ----
    val sameWork_3_2 = generateSameWorkConfigs(3, 2, 2, 6)
    testHypothesis("H3: SAME-WORK STAGES (L=3, n=2, k=2, work 1-6)", sameWork_3_2)

    val sameWork_3_3 = generateSameWorkConfigs(3, 3, 2, 6)
    testHypothesis("H3: SAME-WORK STAGES (L=3, n=3, k=2, work 1-6)", sameWork_3_3)

    // ---- H4: Bounded ratio ----
    // Full enumeration for small instances
    testBoundedRatio(3, 2, 2, 6)

    // n=3 with smaller work range to keep it feasible
    // 4^3 = 64 work vectors per stage, 64^3 = 262144 configs — that's large.
    // Use work 1-3 for n=3.
    testBoundedRatio(3, 3, 2, 3)

    val elapsed = System.currentTimeMillis() - startTime
    println(s"\n${"=" * 80}")
    println(f"  Total elapsed: ${elapsed / 1000.0}%.1f seconds")
    println(s"${"=" * 80}")
