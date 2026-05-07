/**
 * Robustness Simulation: "Even a random shared ordering beats optimized independent orderings X% of the time."
 *
 * Lightweight Monte Carlo simulation for the assembly flow shop model.
 * Generates random configurations and compares shared vs independent orderings
 * on makespan and flowtime, producing statistics for the HBR article.
 *
 * Model:
 *   - m Foundation teams (stage 1, parallel), each with k workers
 *   - 1 Dependent team (stage 2, assembly constraint), with k workers
 *   - n initiatives with heterogeneous work: work(team)(initiative) drawn uniformly from 1..maxWork
 *   - Workers split work evenly: each does ceil(w/k) or floor(w/k), so completion = ceil(w/k)
 *   - Assembly constraint: initiative can't start on dependent team until ALL foundation teams finish it
 *   - Dependent team processes initiatives in a given order, respecting assembly readiness
 */

import scala.util.Random
import scala.collection.mutable

object RobustnessSimulation:

  // --- Core simulation (no object allocation, just arrays) ---

  /**
   * Compute per-initiative completion times on the dependent team.
   *
   * @param foundationWork  foundationWork(t)(i) = work for initiative i on foundation team t
   * @param depWork         depWork(i) = work for initiative i on dependent team
   * @param foundationOrders foundationOrders(t) = ordering (permutation) for foundation team t
   * @param depOrder        ordering for the dependent team
   * @param k               workers per team
   * @return completionTimes(i) = completion time of initiative i on the dependent team
   */
  def simulate(
    foundationWork: Array[Array[Int]],
    depWork: Array[Int],
    foundationOrders: Array[Array[Int]],
    depOrder: Array[Int],
    k: Int
  ): Array[Int] =
    val n = depWork.length
    val m = foundationWork.length

    // Step 1: Compute foundation completion times for each initiative
    // For each foundation team, process initiatives in its ordering.
    // Team completion time for initiative i = cumulative time up to initiative i in that team's order.
    // With k workers splitting evenly: time for initiative = ceil(w / k)
    val foundationCompletion = Array.ofDim[Int](n) // max across foundation teams

    // For each foundation team, compute cumulative completion times
    for t <- 0 until m do
      val order = foundationOrders(t)
      var cumTime = 0
      for pos <- 0 until n do
        val initiative = order(pos)
        val w = foundationWork(t)(initiative)
        val duration = (w + k - 1) / k // ceil(w/k)
        cumTime += duration
        // Assembly time = max across all foundation teams
        foundationCompletion(initiative) = math.max(foundationCompletion(initiative), cumTime)

    // Step 2: Schedule dependent team respecting assembly readiness
    // The dependent team has k workers. For simplicity with equal-split work division,
    // the team processes one initiative at a time (all k workers on the same initiative).
    // Duration = ceil(depWork(i) / k).
    // Start time = max(previous initiative done, assembly ready time).
    val completionTimes = new Array[Int](n)
    var depTime = 0
    for pos <- 0 until n do
      val initiative = depOrder(pos)
      val readyTime = foundationCompletion(initiative)
      val startTime = math.max(depTime, readyTime)
      val duration = (depWork(initiative) + k - 1) / k
      depTime = startTime + duration
      completionTimes(initiative) = depTime

    completionTimes

  /** Compute makespan = max completion time. */
  def makespan(completionTimes: Array[Int]): Int =
    var max = 0
    var i = 0
    while i < completionTimes.length do
      if completionTimes(i) > max then max = completionTimes(i)
      i += 1
    max

  /** Compute flowtime = sum of completion times. */
  def flowtime(completionTimes: Array[Int]): Int =
    var sum = 0
    var i = 0
    while i < completionTimes.length do
      sum += completionTimes(i)
      i += 1
    sum

  // --- Random configuration generation ---

  case class Config(
    foundationWork: Array[Array[Int]], // m x n
    depWork: Array[Int],               // n
    n: Int,
    m: Int,
    k: Int
  )

  def randomConfig(n: Int, m: Int, k: Int, maxWork: Int, rng: Random): Config =
    val foundationWork = Array.fill(m)(Array.fill(n)(rng.nextInt(maxWork) + 1))
    val depWork = Array.fill(n)(rng.nextInt(maxWork) + 1)
    Config(foundationWork, depWork, n, m, k)

  // --- Permutation utilities ---

  /** Generate all permutations of 0 until n. */
  def allPermutations(n: Int): Array[Array[Int]] =
    (0 until n).toArray.permutations.map(_.clone()).toArray

  /** Generate a random permutation of 0 until n. */
  def randomPermutation(n: Int, rng: Random): Array[Int] =
    val a = (0 until n).toArray
    // Fisher-Yates shuffle
    var i = n - 1
    while i > 0 do
      val j = rng.nextInt(i + 1)
      val tmp = a(i)
      a(i) = a(j)
      a(j) = tmp
      i -= 1
    a

  // --- Evaluation helpers ---

  /**
   * Evaluate a shared ordering: all foundation teams + dependent team use the same permutation.
   * Returns (makespan, flowtime).
   */
  def evalShared(config: Config, perm: Array[Int]): (Int, Int) =
    val orders = Array.fill(config.m)(perm)
    val ct = simulate(config.foundationWork, config.depWork, orders, perm, config.k)
    (makespan(ct), flowtime(ct))

  /**
   * Evaluate an independent ordering: each foundation team has its own permutation,
   * dependent team uses a given ordering.
   * Returns (makespan, flowtime).
   */
  def evalIndependent(config: Config, foundationOrders: Array[Array[Int]], depOrder: Array[Int]): (Int, Int) =
    val ct = simulate(config.foundationWork, config.depWork, foundationOrders, depOrder, config.k)
    (makespan(ct), flowtime(ct))

  /**
   * Find the best independent ordering by trying all combinations (small n)
   * or sampling (large n).
   *
   * For independent orderings, each foundation team picks its own permutation.
   * The dependent team tries all n! orderings (small n) or samples.
   * Returns (bestMakespan, bestFlowtime) -- these may come from different schedule combos.
   */
  def bestIndependent(config: Config, rng: Random, maxSamples: Int = 10000): (Int, Int) =
    val n = config.n
    val m = config.m

    if n <= 5 then
      // Enumerate all n!^m foundation combinations x n! dependent orderings
      // For n=5, m=2: 120^2 * 120 = 1,728,000 -- feasible
      // For n=5, m=3: 120^3 * 120 = 207,360,000 -- too many, sample dependent
      // For n=5, m=4: way too many -- sample
      val allPerms = allPermutations(n)
      val totalFoundationCombos = math.pow(allPerms.length.toDouble, m).toLong
      val totalCombos = totalFoundationCombos * allPerms.length

      if totalCombos <= 2_000_000L then
        enumerateAllIndependent(config, allPerms)
      else
        sampleIndependent(config, rng, maxSamples)
    else
      sampleIndependent(config, rng, maxSamples)

  private def enumerateAllIndependent(config: Config, allPerms: Array[Array[Int]]): (Int, Int) =
    val m = config.m
    var bestMs = Int.MaxValue
    var bestFt = Int.MaxValue

    // Generate all m-tuples of permutation indices
    val numPerms = allPerms.length
    val indices = new Array[Int](m)

    def recurse(team: Int): Unit =
      if team == m then
        // We have a foundation ordering combo; try all dependent orderings
        val foundOrders = indices.map(allPerms(_))
        for depPerm <- allPerms do
          val ct = simulate(config.foundationWork, config.depWork, foundOrders, depPerm, config.k)
          val ms = makespan(ct)
          val ft = flowtime(ct)
          if ms < bestMs then bestMs = ms
          if ft < bestFt then bestFt = ft
      else
        var i = 0
        while i < numPerms do
          indices(team) = i
          recurse(team + 1)
          i += 1

    recurse(0)
    (bestMs, bestFt)

  private def sampleIndependent(config: Config, rng: Random, maxSamples: Int): (Int, Int) =
    val n = config.n
    val m = config.m
    var bestMs = Int.MaxValue
    var bestFt = Int.MaxValue

    var s = 0
    while s < maxSamples do
      val foundOrders = Array.fill(m)(randomPermutation(n, rng))
      val depOrder = randomPermutation(n, rng)
      val ct = simulate(config.foundationWork, config.depWork, foundOrders, depOrder, config.k)
      val ms = makespan(ct)
      val ft = flowtime(ct)
      if ms < bestMs then bestMs = ms
      if ft < bestFt then bestFt = ft
      s += 1

    (bestMs, bestFt)

  /**
   * Find the best shared ordering (all teams use the same permutation).
   * For small n, enumerate all n! permutations; for large n, sample.
   */
  def bestShared(config: Config, rng: Random, maxSamples: Int = 10000): (Int, Int) =
    val n = config.n
    if n <= 8 then
      val allPerms = allPermutations(n)
      var bestMs = Int.MaxValue
      var bestFt = Int.MaxValue
      for perm <- allPerms do
        val (ms, ft) = evalShared(config, perm)
        if ms < bestMs then bestMs = ms
        if ft < bestFt then bestFt = ft
      (bestMs, bestFt)
    else
      var bestMs = Int.MaxValue
      var bestFt = Int.MaxValue
      var s = 0
      while s < maxSamples do
        val perm = randomPermutation(n, rng)
        val (ms, ft) = evalShared(config, perm)
        if ms < bestMs then bestMs = ms
        if ft < bestFt then bestFt = ft
        s += 1
      (bestMs, bestFt)

  // --- Main simulation ---

  case class ScenarioResult(
    n: Int,
    m: Int,
    numConfigs: Int,
    // Tier 2: Random shared vs best independent
    // Makespan
    pctRandomSharedBeatsBestIndep_ms: Double,
    pctRandomSharedTiesBestIndep_ms: Double,
    avgGapWhenLoses_ms: Double,   // avg (randomShared - bestIndep) / bestIndep when random loses
    avgGapWhenWins_ms: Double,    // avg (bestIndep - randomShared) / bestIndep when random wins
    medianRatio_ms: Double,       // median(randomShared / bestIndep)
    // Flowtime
    pctRandomSharedBeatsBestIndep_ft: Double,
    pctRandomSharedTiesBestIndep_ft: Double,
    avgGapWhenLoses_ft: Double,
    avgGapWhenWins_ft: Double,
    medianRatio_ft: Double,
    // Tier 1: Best shared vs best independent
    pctBestSharedBeatsBestIndep_ms: Double,
    pctBestSharedBeatsBestIndep_ft: Double,
    // Tier 3: Best shared vs random independent (unordered lists)
    avgGapBestSharedVsRandomIndep_ms: Double,     // avg % gap (bestShared - randomIndep) / randomIndep * 100
    avgGapBestSharedVsRandomIndep_ft: Double,
    pctBestSharedBeatsRandomIndep_ms: Double,      // % of time best shared <= random independent
    pctBestSharedBeatsRandomIndep_ft: Double,
    medianGapBestSharedVsRandomIndep_ms: Double,   // median % improvement
    worstGapBestSharedVsRandomIndep_ms: Double,    // worst case % gap (largest improvement best shared achieves)
    // Tier 4: Random shared vs random independent (imperfect vs imperfect)
    pctRandomSharedBeatsRandomIndep_ms: Double,
    pctRandomSharedBeatsRandomIndep_ft: Double,
    avgGapRandomSharedVsRandomIndep_ms: Double,    // avg % gap when random shared beats random indep
    avgGapRandomSharedVsRandomIndep_ft: Double,
    medianGapRandomSharedVsRandomIndep_ms: Double
  )

  /**
   * Generate a random independent ordering: each foundation team picks a random permutation,
   * dependent team picks a random permutation. Returns (makespan, flowtime).
   */
  def evalRandomIndependent(config: Config, rng: Random): (Int, Int) =
    val foundOrders = Array.fill(config.m)(randomPermutation(config.n, rng))
    val depOrder = randomPermutation(config.n, rng)
    evalIndependent(config, foundOrders, depOrder)

  def runScenario(n: Int, m: Int, k: Int, numConfigs: Int, numRandomShared: Int, rng: Random): ScenarioResult =
    val maxWork = 10
    val numRandomIndep = numRandomShared // same sample count for random independent orderings

    // Tier 2: Accumulators for random-shared vs best-independent
    var totalRandomTrials = 0L
    var msWins = 0L
    var msTies = 0L
    var msLosses = 0L
    var ftWins = 0L
    var ftTies = 0L
    var ftLosses = 0L

    val msGapWhenLoses = mutable.ArrayBuffer[Double]()
    val msGapWhenWins = mutable.ArrayBuffer[Double]()
    val ftGapWhenLoses = mutable.ArrayBuffer[Double]()
    val ftGapWhenWins = mutable.ArrayBuffer[Double]()
    val msRatios = mutable.ArrayBuffer[Double]()
    val ftRatios = mutable.ArrayBuffer[Double]()

    // Tier 1: Best shared vs best independent
    var bestSharedBeatsBestIndepMs = 0
    var bestSharedBeatsBestIndepFt = 0

    // Tier 3: Best shared vs random independent (unordered lists)
    var t3Trials = 0L
    var t3BestSharedBeatsMs = 0L
    var t3BestSharedBeatsFt = 0L
    val t3GapMs = mutable.ArrayBuffer[Double]()  // (randomIndep - bestShared) / randomIndep * 100
    val t3GapFt = mutable.ArrayBuffer[Double]()

    // Tier 4: Random shared vs random independent (imperfect vs imperfect)
    var t4Trials = 0L
    var t4RandSharedBeatsMs = 0L
    var t4RandSharedBeatsFt = 0L
    val t4GapMs = mutable.ArrayBuffer[Double]()  // (randomIndep - randomShared) / randomIndep * 100
    val t4GapFt = mutable.ArrayBuffer[Double]()

    var c = 0
    while c < numConfigs do
      val config = randomConfig(n, m, k, maxWork, rng)

      // Find best independent ordering
      val (bestIndepMs, bestIndepFt) = bestIndependent(config, rng)

      // Find best shared ordering
      val (bestSharedMs, bestSharedFt) = bestShared(config, rng)

      if bestSharedMs <= bestIndepMs then bestSharedBeatsBestIndepMs += 1
      if bestSharedFt <= bestIndepFt then bestSharedBeatsBestIndepFt += 1

      // Tier 3: Compare best shared vs random independent orderings
      var ri = 0
      while ri < numRandomIndep do
        val (randIndepMs, randIndepFt) = evalRandomIndependent(config, rng)
        t3Trials += 1

        if bestSharedMs <= randIndepMs then t3BestSharedBeatsMs += 1
        if bestSharedFt <= randIndepFt then t3BestSharedBeatsFt += 1

        // Gap: how much better is best shared? Positive = best shared wins
        if randIndepMs > 0 then
          t3GapMs += (randIndepMs - bestSharedMs).toDouble / randIndepMs * 100.0
        if randIndepFt > 0 then
          t3GapFt += (randIndepFt - bestSharedFt).toDouble / randIndepFt * 100.0

        ri += 1

      // Sample random shared orderings (for Tier 2 and Tier 4)
      var s = 0
      while s < numRandomShared do
        val perm = randomPermutation(n, rng)
        val (randMs, randFt) = evalShared(config, perm)

        totalRandomTrials += 1

        // Tier 2: Makespan comparison vs best independent
        if randMs < bestIndepMs then
          msWins += 1
          msGapWhenWins += (bestIndepMs - randMs).toDouble / bestIndepMs
        else if randMs == bestIndepMs then
          msTies += 1
        else
          msLosses += 1
          msGapWhenLoses += (randMs - bestIndepMs).toDouble / bestIndepMs

        msRatios += randMs.toDouble / bestIndepMs

        // Tier 2: Flowtime comparison vs best independent
        if randFt < bestIndepFt then
          ftWins += 1
          ftGapWhenWins += (bestIndepFt - randFt).toDouble / bestIndepFt
        else if randFt == bestIndepFt then
          ftTies += 1
        else
          ftLosses += 1
          ftGapWhenLoses += (randFt - bestIndepFt).toDouble / bestIndepFt

        ftRatios += randFt.toDouble / bestIndepFt

        // Tier 4: Compare this random shared vs a fresh random independent
        val (randIndepMs, randIndepFt) = evalRandomIndependent(config, rng)
        t4Trials += 1

        if randMs <= randIndepMs then t4RandSharedBeatsMs += 1
        if randFt <= randIndepFt then t4RandSharedBeatsFt += 1

        if randIndepMs > 0 then
          t4GapMs += (randIndepMs - randMs).toDouble / randIndepMs * 100.0
        if randIndepFt > 0 then
          t4GapFt += (randIndepFt - randFt).toDouble / randIndepFt * 100.0

        s += 1

      c += 1
      if c % 1000 == 0 then
        System.err.print(s"\r  n=$n m=$m: $c / $numConfigs configs done")

    System.err.println(s"\r  n=$n m=$m: $numConfigs / $numConfigs configs done")

    val total = totalRandomTrials.toDouble
    val t3Total = t3Trials.toDouble
    val t4Total = t4Trials.toDouble

    ScenarioResult(
      n = n,
      m = m,
      numConfigs = numConfigs,
      // Tier 2
      pctRandomSharedBeatsBestIndep_ms = (msWins + msTies) / total * 100.0,
      pctRandomSharedTiesBestIndep_ms = msTies / total * 100.0,
      avgGapWhenLoses_ms = if msGapWhenLoses.nonEmpty then msGapWhenLoses.sum / msGapWhenLoses.size * 100.0 else 0.0,
      avgGapWhenWins_ms = if msGapWhenWins.nonEmpty then msGapWhenWins.sum / msGapWhenWins.size * 100.0 else 0.0,
      medianRatio_ms = median(msRatios.toArray),
      pctRandomSharedBeatsBestIndep_ft = (ftWins + ftTies) / total * 100.0,
      pctRandomSharedTiesBestIndep_ft = ftTies / total * 100.0,
      avgGapWhenLoses_ft = if ftGapWhenLoses.nonEmpty then ftGapWhenLoses.sum / ftGapWhenLoses.size * 100.0 else 0.0,
      avgGapWhenWins_ft = if ftGapWhenWins.nonEmpty then ftGapWhenWins.sum / ftGapWhenWins.size * 100.0 else 0.0,
      medianRatio_ft = median(ftRatios.toArray),
      // Tier 1
      pctBestSharedBeatsBestIndep_ms = bestSharedBeatsBestIndepMs.toDouble / numConfigs * 100.0,
      pctBestSharedBeatsBestIndep_ft = bestSharedBeatsBestIndepFt.toDouble / numConfigs * 100.0,
      // Tier 3
      avgGapBestSharedVsRandomIndep_ms = if t3GapMs.nonEmpty then t3GapMs.sum / t3GapMs.size else 0.0,
      avgGapBestSharedVsRandomIndep_ft = if t3GapFt.nonEmpty then t3GapFt.sum / t3GapFt.size else 0.0,
      pctBestSharedBeatsRandomIndep_ms = t3BestSharedBeatsMs / t3Total * 100.0,
      pctBestSharedBeatsRandomIndep_ft = t3BestSharedBeatsFt / t3Total * 100.0,
      medianGapBestSharedVsRandomIndep_ms = median(t3GapMs.toArray),
      worstGapBestSharedVsRandomIndep_ms = if t3GapMs.nonEmpty then t3GapMs.max else 0.0,
      // Tier 4
      pctRandomSharedBeatsRandomIndep_ms = t4RandSharedBeatsMs / t4Total * 100.0,
      pctRandomSharedBeatsRandomIndep_ft = t4RandSharedBeatsFt / t4Total * 100.0,
      avgGapRandomSharedVsRandomIndep_ms = if t4GapMs.nonEmpty then t4GapMs.sum / t4GapMs.size else 0.0,
      avgGapRandomSharedVsRandomIndep_ft = if t4GapFt.nonEmpty then t4GapFt.sum / t4GapFt.size else 0.0,
      medianGapRandomSharedVsRandomIndep_ms = median(t4GapMs.toArray)
    )

  private def median(arr: Array[Double]): Double =
    val sorted = arr.sorted
    val n = sorted.length
    if n == 0 then 0.0
    else if n % 2 == 1 then sorted(n / 2)
    else (sorted(n / 2 - 1) + sorted(n / 2)) / 2.0

  // --- Printing ---

  def printResults(results: List[ScenarioResult]): Unit =
    println()
    println("=" * 130)
    println("ROBUSTNESS SIMULATION: Shared vs Independent Orderings (Four-Tier Comparison)")
    println("Assembly flow shop: m foundation teams (stage 1) + 1 dependent team (stage 2), k=2 workers/team")
    println("Work drawn uniformly from 1..10 per initiative per team")
    println("=" * 130)

    // Tier 1: Best shared vs best independent
    println()
    println("TIER 1: Best Shared vs Best Independent (the theorem result)")
    println("  'How much does optimal coordination beat optimal independence?'")
    println()
    println(f"${"n"}%3s ${"m"}%3s | ${"Configs"}%7s | ${"BestS>=BestI (ms)"}%18s | ${"BestS>=BestI (ft)"}%18s")
    println("-" * 60)
    for r <- results do
      val ms = f"${r.pctBestSharedBeatsBestIndep_ms}%.1f%%"
      val ft = f"${r.pctBestSharedBeatsBestIndep_ft}%.1f%%"
      println(f"${r.n}%3d ${r.m}%3d | ${r.numConfigs}%7d | ${ms}%18s | ${ft}%18s")
    println()

    // Tier 2: Random shared vs best independent
    println("TIER 2: Random Shared vs Best Independent (the '7-15%% gap' result)")
    println("  'Even a random shared ordering beats optimized independent orderings X%% of the time.'")
    println()
    println(f"${"n"}%3s ${"m"}%3s | ${"Configs"}%7s | ${"Rand>=Best"}%10s | ${"Strict Win"}%10s | ${"Tie"}%8s | ${"Avg Gap (lose)"}%14s | ${"Avg Gap (win)"}%13s | ${"Med Ratio"}%9s")
    println("-" * 110)
    for r <- results do
      val pctWinOrTie = f"${r.pctRandomSharedBeatsBestIndep_ms}%.1f%%"
      val pctStrictWin = f"${r.pctRandomSharedBeatsBestIndep_ms - r.pctRandomSharedTiesBestIndep_ms}%.1f%%"
      val pctTie = f"${r.pctRandomSharedTiesBestIndep_ms}%.1f%%"
      val gapLose = f"${r.avgGapWhenLoses_ms}%.1f%%"
      val gapWin = f"${r.avgGapWhenWins_ms}%.1f%%"
      val medRatio = f"${r.medianRatio_ms}%.4f"
      println(f"${r.n}%3d ${r.m}%3d | ${r.numConfigs}%7d | ${pctWinOrTie}%10s | ${pctStrictWin}%10s | ${pctTie}%8s | ${gapLose}%14s | ${gapWin}%13s | ${medRatio}%9s")
    println()

    // Tier 3: Best shared vs random independent (unordered lists)
    println("TIER 3: Best Shared vs Random Independent (the 'unordered lists' gap)")
    println("  'How much worse is it when teams have no ordering guidance at all?'")
    println()
    println(f"${"n"}%3s ${"m"}%3s | ${"Configs"}%7s | ${"BestS wins (ms)"}%15s | ${"BestS wins (ft)"}%15s | ${"Avg gap (ms)"}%12s | ${"Avg gap (ft)"}%12s | ${"Med gap (ms)"}%12s | ${"Worst gap (ms)"}%15s")
    println("-" * 120)
    for r <- results do
      val winsMs = f"${r.pctBestSharedBeatsRandomIndep_ms}%.1f%%"
      val winsFt = f"${r.pctBestSharedBeatsRandomIndep_ft}%.1f%%"
      val avgMs = f"${r.avgGapBestSharedVsRandomIndep_ms}%.1f%%"
      val avgFt = f"${r.avgGapBestSharedVsRandomIndep_ft}%.1f%%"
      val medMs = f"${r.medianGapBestSharedVsRandomIndep_ms}%.1f%%"
      val worstMs = f"${r.worstGapBestSharedVsRandomIndep_ms}%.1f%%"
      println(f"${r.n}%3d ${r.m}%3d | ${r.numConfigs}%7d | ${winsMs}%15s | ${winsFt}%15s | ${avgMs}%12s | ${avgFt}%12s | ${medMs}%12s | ${worstMs}%15s")
    println()

    // Tier 4: Random shared vs random independent (imperfect vs imperfect)
    println("TIER 4: Random Shared vs Random Independent (imperfect vs imperfect)")
    println("  'If neither side optimizes, how often does shared ordering still win?'")
    println()
    println(f"${"n"}%3s ${"m"}%3s | ${"Configs"}%7s | ${"RandS wins (ms)"}%15s | ${"RandS wins (ft)"}%15s | ${"Avg gap (ms)"}%12s | ${"Avg gap (ft)"}%12s | ${"Med gap (ms)"}%12s")
    println("-" * 100)
    for r <- results do
      val winsMs = f"${r.pctRandomSharedBeatsRandomIndep_ms}%.1f%%"
      val winsFt = f"${r.pctRandomSharedBeatsRandomIndep_ft}%.1f%%"
      val avgMs = f"${r.avgGapRandomSharedVsRandomIndep_ms}%.1f%%"
      val avgFt = f"${r.avgGapRandomSharedVsRandomIndep_ft}%.1f%%"
      val medMs = f"${r.medianGapRandomSharedVsRandomIndep_ms}%.1f%%"
      println(f"${r.n}%3d ${r.m}%3d | ${r.numConfigs}%7d | ${winsMs}%15s | ${winsFt}%15s | ${avgMs}%12s | ${avgFt}%12s | ${medMs}%12s")
    println()

    // Summary for HBR
    println("=" * 130)
    println("KEY FINDINGS FOR HBR ARTICLE")
    println("=" * 130)
    println()
    println("Tier 1 (Theorem): Best shared vs best independent")
    for r <- results do
      println(f"  n=${r.n}%d, m=${r.m}%d: Best shared ordering >= best independent ${r.pctBestSharedBeatsBestIndep_ms}%.1f%% (ms), ${r.pctBestSharedBeatsBestIndep_ft}%.1f%% (ft)")
    println()
    println("Tier 2 (Practical): Random shared vs best independent")
    for r <- results do
      val pctBeat = r.pctRandomSharedBeatsBestIndep_ms
      println(f"  n=${r.n}%d, m=${r.m}%d: Random shared >= best independent ${pctBeat}%.1f%% of the time (makespan)")
    println()
    println("Tier 3 (Unordered lists): Best shared vs random independent")
    for r <- results do
      println(f"  n=${r.n}%d, m=${r.m}%d: Best shared beats random independent ${r.pctBestSharedBeatsRandomIndep_ms}%.1f%% of the time, avg improvement ${r.avgGapBestSharedVsRandomIndep_ms}%.1f%%, worst case ${r.worstGapBestSharedVsRandomIndep_ms}%.1f%%")
    println()
    println("Tier 4 (Imperfect vs imperfect): Random shared vs random independent")
    for r <- results do
      println(f"  n=${r.n}%d, m=${r.m}%d: Random shared beats random independent ${r.pctRandomSharedBeatsRandomIndep_ms}%.1f%% of the time, avg gap ${r.avgGapRandomSharedVsRandomIndep_ms}%.1f%%")
    println()

  // --- Main ---

  def main(args: Array[String]): Unit =
    val seed = if args.length > 0 then args(0).toLong else 42L
    val rng = new Random(seed)

    // Configuration: (n, m) combinations
    // k=2 throughout (matches the paper's model)
    val k = 2
    val scenarios = List(
      (3, 2), (3, 3), (3, 4),
      (4, 2), (4, 3), (4, 4),
      (5, 2), (5, 3),
      (6, 2), (6, 3),
      (7, 2),
      (8, 2)
    )

    // Adjust number of configs and random samples based on n
    // For small n we can afford more configs; for large n we need fewer
    // because bestIndependent enumeration/sampling is expensive
    def numConfigs(n: Int, m: Int): Int =
      if n <= 4 then 10000
      else if n <= 5 then 5000
      else if n <= 6 then 2000
      else if n <= 7 then 1000
      else 500

    val numRandomShared = 100  // random shared orderings per config

    println(s"Robustness Simulation (seed=$seed, k=$k)")
    println(s"Scenarios: ${scenarios.map((n,m) => s"(n=$n,m=$m)").mkString(", ")}")
    println()

    val startTime = System.currentTimeMillis()

    val results = scenarios.map { (n, m) =>
      val nc = numConfigs(n, m)
      System.err.println(s"Starting n=$n, m=$m ($nc configs, $numRandomShared random shared each)")
      val t0 = System.currentTimeMillis()
      val result = runScenario(n, m, k, nc, numRandomShared, rng)
      val elapsed = System.currentTimeMillis() - t0
      System.err.println(f"  Completed in ${elapsed / 1000.0}%.1f s")
      result
    }

    val totalElapsed = System.currentTimeMillis() - startTime
    println(f"Total simulation time: ${totalElapsed / 1000.0}%.1f s")

    printResults(results)
