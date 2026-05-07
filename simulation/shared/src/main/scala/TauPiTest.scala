/**
 * TauPiTest: Does tau=pi always minimize C_max at stage 2?
 *
 * Model: Two-stage assembly flow shop with k identical workers per machine.
 *   Stage 1: m parallel machines, each with k workers
 *   Stage 2: 1 machine with k workers
 *   Work w_{i,j} is divisible among k workers => processing time p_{i,j} = ceil(w_{i,j}/k)
 *
 * Given a permutation pi of jobs at stage 1 (all machines use the same order = synchronized):
 *   - Water-filling gives release times r*_{pi(j)} for each job at stage 2
 *   - r*_{pi(1)} <= r*_{pi(2)} <= ... <= r*_{pi(n)} by construction
 *
 * Question: Is FIFO at stage 2 (tau = pi) always C_max-optimal?
 *   i.e., among all permutations tau, does tau=pi minimize
 *     C_max = max over s of { max(C^2_{tau(s-1)}, r*_{tau(s)}) + q_{tau(s)} }
 *   where C^2_0 = 0?
 *
 * We test this exhaustively for small instances.
 */
object TauPiTest:

  /** Compute stage-1 processing time on machine i for job j: ceil(w/k) */
  def procTime(w: Int, k: Int): Int = (w + k - 1) / k

  /**
   * Given a permutation pi of jobs, compute the water-filling release times.
   *
   * Stage 1 has m machines, each with k workers.
   * w(i)(j) = work for job j on machine i (0-indexed).
   * Jobs are processed in order pi on every machine.
   *
   * On each machine i, jobs are processed sequentially in pi-order:
   *   completion_{i, pi(s)} = completion_{i, pi(s-1)} + ceil(w_{i, pi(s)} / k)
   *
   * Release time for job pi(s) = max over machines i of completion_{i, pi(s)}.
   */
  def computeReleaseTimes(
    pi: Array[Int],       // permutation of job indices
    w: Array[Array[Int]], // w(i)(j) = work on machine i for job j
    m: Int,
    k: Int
  ): Array[Double] =
    val n = pi.length
    val release = new Array[Double](n)
    val machineCompletion = new Array[Double](m)

    for s <- 0 until n do
      val job = pi(s)
      var maxCompletion = 0.0
      for i <- 0 until m do
        machineCompletion(i) = machineCompletion(i) + procTime(w(i)(job), k)
        maxCompletion = math.max(maxCompletion, machineCompletion(i))
      release(job) = maxCompletion

    release

  /**
   * Compute C_max at stage 2 for a given tau ordering and release times.
   * q(j) = processing time for job j at stage 2 = ceil(assemblyWork(j) / k)
   *
   * Recurrence: C^2_{tau(s)} = max(C^2_{tau(s-1)}, r*_{tau(s)}) + q_{tau(s)}
   * C_max = C^2_{tau(n-1)}
   */
  def computeCmax(
    tau: Array[Int],
    releaseTimes: Array[Double],
    q: Array[Double]
  ): Double =
    var cmax = 0.0
    for s <- 0 until tau.length do
      val job = tau(s)
      cmax = math.max(cmax, releaseTimes(job)) + q(job)
    cmax

  /** Generate all permutations of 0 until n */
  def allPerms(n: Int): Array[Array[Int]] =
    (0 until n).toArray.permutations.toArray

  case class Instance(
    n: Int, m: Int, k: Int,
    w: Array[Array[Int]],   // w(machine)(job)
    qWork: Array[Int]       // stage-2 work per job
  )

  case class TestResult(
    instance: Instance,
    pi: Array[Int],
    releaseTimes: Array[Double],
    cmaxPiEqualsTau: Double,
    cmaxOptimalTau: Double,
    optimalTau: Array[Int],
    fifoOptimal: Boolean
  )

  /**
   * For a given instance and a given pi, check whether tau=pi is C_max-optimal.
   */
  def testPi(inst: Instance, pi: Array[Int]): TestResult =
    val release = computeReleaseTimes(pi, inst.w, inst.m, inst.k)
    val q = inst.qWork.map(qw => procTime(qw, inst.k).toDouble)

    // C_max with tau = pi
    val cmaxFifo = computeCmax(pi, release, q)

    // Find optimal tau over all n! permutations
    var bestCmax = Double.MaxValue
    var bestTau = pi
    for tau <- allPerms(inst.n) do
      val c = computeCmax(tau, release, q)
      if c < bestCmax then
        bestCmax = c
        bestTau = tau

    TestResult(
      instance = inst,
      pi = pi,
      releaseTimes = release,
      cmaxPiEqualsTau = cmaxFifo,
      cmaxOptimalTau = bestCmax,
      optimalTau = bestTau,
      fifoOptimal = cmaxFifo <= bestCmax + 1e-9
    )

  def main(args: Array[String]): Unit =
    println("=" * 78)
    println("TAU = PI TEST: Is FIFO at stage 2 always C_max-optimal?")
    println("=" * 78)
    println()

    var totalTests = 0L
    var totalFailures = 0L
    var totalInstances = 0L

    val failures = scala.collection.mutable.ListBuffer[TestResult]()
    val rng = new scala.util.Random(42)

    // Parameter sweep
    for
      n <- 2 to 4
      m <- 2 to 3
      k <- 2 to 3
    do
      val configLabel = s"n=$n, m=$m, k=$k"
      var configTests = 0L
      var configFailures = 0L
      var configInstances = 0L

      val workVals = List(1, 2, 3, 5, 7, 10)
      val qVals = List(1, 2, 3, 5, 7, 10)

      // --- Structured instances ---

      // 1. Uniform work across machines, systematic over small value set
      val smallWork = if n <= 3 then List(1, 3, 5, 10) else List(1, 3, 7)
      val smallQ = if n <= 3 then List(1, 3, 5, 10) else List(1, 3, 7)

      val uniformInstances = for
        wVals <- tuples(smallWork, n)
        qVals <- tuples(smallQ, n)
      yield Instance(n, m, k, Array.fill(m)(wVals.toArray), qVals.toArray)

      // 2. Random heterogeneous instances
      val numRandom = if n <= 3 then 500 else 200
      val randomInstances = (0 until numRandom).map { _ =>
        val w = Array.tabulate(m)(_ => Array.tabulate(n)(_ => workVals(rng.nextInt(workVals.size))))
        val qWork = Array.tabulate(n)(_ => qVals(rng.nextInt(qVals.size)))
        Instance(n, m, k, w, qWork)
      }

      // 3. Adversarial instances
      val adversarial = scala.collection.mutable.ListBuffer[Instance]()
      for i <- 0 until n do
        // Large q_i, small others; small stage-1 for i
        adversarial += Instance(n, m, k,
          Array.tabulate(m)(_ => Array.tabulate(n)(j => if j == i then 1 else 10)),
          Array.tabulate(n)(j => if j == i then 10 else 1))
        // Small q_i, large others
        adversarial += Instance(n, m, k,
          Array.tabulate(m)(_ => Array.tabulate(n)(j => if j == i then 10 else 1)),
          Array.tabulate(n)(j => if j == i then 1 else 10))
        // Mixed machines: one machine has big work for i, another has small
        if m >= 2 then
          adversarial += Instance(n, m, k,
            Array.tabulate(m)(mi => Array.tabulate(n)(j =>
              if mi == 0 && j == i then 10
              else if mi == 1 && j == i then 1
              else 5)),
            Array.tabulate(n)(j => if j == i then 7 else 3))

      val allInstances = uniformInstances ++ randomInstances ++ adversarial.toList

      // Test each instance with ALL permutations pi
      val allPi = allPerms(n)

      for inst <- allInstances do
        configInstances += 1
        for pi <- allPi do
          configTests += 1
          val result = testPi(inst, pi)
          if !result.fifoOptimal then
            configFailures += 1
            if failures.size < 20 then failures += result

      totalTests += configTests
      totalFailures += configFailures
      totalInstances += configInstances

      val status = if configFailures == 0 then "PASS" else s"FAIL (${configFailures} failures)"
      println(f"  $configLabel%-20s  instances=${configInstances}%6d  tests=${configTests}%8d  $status")

    println()
    println("=" * 78)
    println("RESULTS")
    println("=" * 78)
    println(s"  Total instances tested:   ${totalInstances}")
    println(s"  Total (pi, instance) pairs: ${totalTests}")
    println(s"  Failures (tau=pi not C_max-optimal): ${totalFailures}")
    println()

    if failures.isEmpty then
      println("  CONCLUSION: tau=pi is ALWAYS C_max-optimal across all tested instances.")
      println("  FIFO at stage 2 (processing jobs in release-time order) minimizes makespan.")
    else
      println(s"  CONCLUSION: tau=pi is NOT always C_max-optimal! Found counterexamples.")
      println()
      for (f, i) <- failures.take(10).zipWithIndex do
        println(s"  --- Counterexample ${i+1} ---")
        println(s"  n=${f.instance.n}, m=${f.instance.m}, k=${f.instance.k}")
        for mi <- 0 until f.instance.m do
          println(s"    Machine $mi work: ${f.instance.w(mi).mkString(", ")}")
        println(s"    Stage-2 work:    ${f.instance.qWork.mkString(", ")}")
        println(s"    pi  = [${f.pi.mkString(", ")}]")
        println(s"    Release times r*: ${f.releaseTimes.map(r => f"$r%.1f").mkString(", ")}")
        println(s"    C_max(tau=pi)      = ${f.cmaxPiEqualsTau}")
        println(s"    C_max(optimal tau) = ${f.cmaxOptimalTau}  tau=[${f.optimalTau.mkString(", ")}]")
        println(s"    Gap = ${f.cmaxPiEqualsTau - f.cmaxOptimalTau}")
        println()

    println()

  /** Generate all tuples of `count` elements drawn from `values` (with repetition). */
  def tuples(values: List[Int], count: Int): List[List[Int]] =
    if count == 0 then List(Nil)
    else
      for
        v <- values
        rest <- tuples(values, count - 1)
      yield v :: rest
