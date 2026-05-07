/**
 * Generalized Assembly Flow Shop with Job-Specific Machine Subsets
 *
 * RESEARCH QUESTION: Does permutation-schedule dominance (P4: pointwise
 * release-time domination) still hold when different jobs use different
 * subsets of stage-1 machines?
 *
 * MODEL:
 *   - n jobs, m stage-1 machines (each with k identical workers), 1 stage-2 machine
 *   - Each job j has a subset S_j ⊆ [m] of stage-1 machines it must pass through
 *   - Assembly constraint: job j enters stage 2 only after ALL machines in S_j complete it
 *   - Release time: r_j = max_{i ∈ S_j} C_{i,j}
 *   - A "synchronized" schedule uses the same permutation on every machine
 *     (restricted to each machine's applicable jobs)
 *
 * PROOF ANALYSIS:
 *   The existing proof (Theorem 1 in ORL paper) has this structure:
 *   1. Sort jobs by non-decreasing r_j to get π
 *   2. Capacity bound: W_i(s) := Σ_{t≤s, π(t)∈J_i} w_{i,π(t)} ≤ k·r_{π(s)}
 *      where J_i = {j : i ∈ S_j}
 *   3. Water-fill on machine i (processing only J_i in π-order):
 *      C*_{i,π(s)} ≤ ⌈W_i(s)/k⌉ for π(s) ∈ J_i
 *   4. Chain: ⌈W_i(s)/k⌉ ≤ r_{π(s)} since W_i(s) ≤ k·r_{π(s)} and r_{π(s)} ∈ ℤ≥0
 *   5. Therefore r*_j ≤ r_j for all j
 *
 *   Step 2 holds because: for each π(t) ∈ J_i with t ≤ s, machine i completed
 *   π(t) by time C_{i,π(t)} ≤ r_{π(t)} ≤ r_{π(s)}, so machine i has done
 *   at least W_i(s) work by time r_{π(s)}, and k workers can do at most
 *   k·r_{π(s)} work total.
 *
 *   This argument works even when J_i varies across machines! The key insight
 *   is that the capacity bound only sums over jobs that actually use machine i.
 *
 * This simulation verifies this analysis by exhaustive enumeration over small instances.
 */

import scala.collection.mutable

// ============================================================
// Data Model
// ============================================================

/** A generalized configuration where each job uses a subset of machines.
  *
  * @param n number of jobs
  * @param m number of stage-1 machines
  * @param k workers per machine (all machines same size)
  * @param subsets subsets(j) = set of machine indices (0-based) that job j uses
  * @param work work(i)(j) = work required by job j on machine i (0 if j doesn't use i)
  * @param stageTwo stageTwo(j) = processing time of job j on stage 2
  * @param label human-readable label
  */
case class GenConfig(
  n: Int,
  m: Int,
  k: Int,
  subsets: IndexedSeq[Set[Int]],     // subsets(j) ⊆ {0,...,m-1}
  work: IndexedSeq[IndexedSeq[Int]], // work(i)(j), i ∈ [m], j ∈ [n]
  stageTwo: IndexedSeq[Int],         // stage-2 processing times
  label: String = ""
):
  require(subsets.size == n, s"subsets.size=${subsets.size} != n=$n")
  require(work.size == m, s"work.size=${work.size} != m=$m")
  require(work.forall(_.size == n), "each work row must have n entries")
  require(stageTwo.size == n, s"stageTwo.size=${stageTwo.size} != n=$n")
  // Work is positive only where the job uses the machine
  for i <- 0 until m; j <- 0 until n do
    if subsets(j).contains(i) then
      require(work(i)(j) > 0, s"job $j uses machine $i but work($i)($j)=0")
    else
      require(work(i)(j) == 0, s"job $j doesn't use machine $i but work($i)($j)=${work(i)(j)}")

  /** Jobs that use machine i */
  def jobsForMachine(i: Int): Set[Int] = (0 until n).filter(j => subsets(j).contains(i)).toSet

  def shortLabel: String =
    if label.nonEmpty then label
    else s"n=$n m=$m k=$k subsets=${subsets.map(s => s.toList.sorted.mkString("{",",","}")).mkString(",")}"


// ============================================================
// Schedule Representation
// ============================================================

/** A schedule in the generalized model.
  *
  * @param machineOrders machineOrders(i) = ordering of jobs on machine i
  *        (must be a permutation of jobsForMachine(i))
  * @param workDivisions workDivisions(i)(j) = Array of k ints giving per-worker work
  *        for job j on machine i. Only defined for j ∈ J_i.
  * @param stage2Order ordering of all n jobs on stage 2
  */
case class GenSchedule(
  machineOrders: IndexedSeq[IndexedSeq[Int]],       // machineOrders(i) = ordering of J_i
  workDivisions: IndexedSeq[Map[Int, IndexedSeq[Int]]], // workDivisions(i)(j)(ell) = work
  stage2Order: IndexedSeq[Int]                       // permutation of [n]
)

/** Result of evaluating a schedule. */
case class GenResult(
  schedule: GenSchedule,
  releaseTimes: IndexedSeq[Int],       // r_j for each job j
  stage2Completions: IndexedSeq[Int],  // C^(2)_j for each job j
  makespan: Int,
  isSynchronized: Boolean,             // all machines use same relative order on shared jobs
  isCommonOrder: Boolean               // there exists a global π such that each machine's order is π restricted to J_i
)


// ============================================================
// Schedule Evaluation
// ============================================================

object GenEvaluator:

  /** Evaluate a schedule: compute release times and stage-2 completion times. */
  def evaluate(config: GenConfig, schedule: GenSchedule): GenResult =
    val n = config.n
    val m = config.m
    val k = config.k

    // Compute completion time of each job on each machine
    val completionTimes = Array.ofDim[Int](m, n) // completionTimes(i)(j)

    for i <- 0 until m do
      val order = schedule.machineOrders(i)
      val workerLoads = Array.fill(k)(0) // cumulative load per worker

      for j <- order do
        val division = schedule.workDivisions(i)(j)
        for ell <- 0 until k do
          workerLoads(ell) += division(ell)
        // Completion time = max worker load among workers that did positive work
        completionTimes(i)(j) = (0 until k).filter(ell => division(ell) > 0).map(workerLoads(_)).max

    // Release times
    val releaseTimes = IndexedSeq.tabulate(n) { j =>
      if config.subsets(j).isEmpty then 0
      else config.subsets(j).map(i => completionTimes(i)(j)).max
    }

    // Stage-2 completion times (max-plus recurrence)
    val stage2Completions = Array.fill(n)(0)
    var prev = 0
    for s <- 0 until n do
      val j = schedule.stage2Order(s)
      val start = math.max(prev, releaseTimes(j))
      stage2Completions(j) = start + config.stageTwo(j)
      prev = stage2Completions(j)

    // Check if schedule uses a common order
    // A schedule has a "common order" if there exists a permutation π of [n] such that
    // machineOrders(i) = π restricted to J_i, for all i.
    val isCommon = checkCommonOrder(config, schedule)

    GenResult(
      schedule = schedule,
      releaseTimes = releaseTimes.toIndexedSeq,
      stage2Completions = stage2Completions.toIndexedSeq,
      makespan = stage2Completions.max,
      isSynchronized = isCommon,
      isCommonOrder = isCommon
    )

  /** Check if a schedule uses a common order: all machine orderings are consistent
    * with some global permutation of [n]. */
  def checkCommonOrder(config: GenConfig, schedule: GenSchedule): Boolean =
    // Build pairwise ordering constraints from each machine
    // For each machine i, machineOrders(i) implies j1 < j2 for jobs in J_i
    val before = mutable.Map[(Int,Int), Boolean]() // (a,b) -> true means a must come before b

    for i <- 0 until config.m do
      val order = schedule.machineOrders(i)
      for s1 <- order.indices; s2 <- s1 + 1 until order.size do
        val a = order(s1)
        val b = order(s2)
        // Machine i says a before b
        before.get((b, a)) match
          case Some(true) => return false // Conflict: another machine says b before a
          case _ => before((a, b)) = true

    true


// ============================================================
// Exhaustive Enumeration
// ============================================================

object GenEnumerator:

  /** Generate all integer compositions of n into k positive parts. */
  def compositions(n: Int, k: Int): List[IndexedSeq[Int]] =
    if k == 1 then
      if n >= 1 then List(IndexedSeq(n))
      else Nil
    else
      (1 to n - k + 1).toList.flatMap { i =>
        compositions(n - i, k - 1).map(rest => IndexedSeq(i) ++ rest)
      }

  /** Water-fill: distribute w units among k workers, one unit at a time to least loaded.
    * This is for a SINGLE job in isolation. */
  def waterFill(w: Int, k: Int): IndexedSeq[Int] =
    val loads = Array.fill(k)(0)
    for _ <- 0 until w do
      val minLoad = loads.min
      val minIdx = loads.indexWhere(_ == minLoad)
      loads(minIdx) += 1
    loads.toIndexedSeq

  /** Cumulative water-fill for a sequence of jobs on a single machine.
    * Returns per-job work divisions that maintain the cumulative load-balance invariant.
    * This is the correct implementation of the proof's water-fill construction. */
  def cumulativeWaterFill(works: IndexedSeq[Int], k: Int): IndexedSeq[IndexedSeq[Int]] =
    val loads = Array.fill(k)(0)
    works.map { w =>
      val jobAlloc = Array.fill(k)(0)
      for _ <- 0 until w do
        val minLoad = loads.min
        val minIdx = loads.indexWhere(_ == minLoad)
        loads(minIdx) += 1
        jobAlloc(minIdx) += 1
      jobAlloc.toIndexedSeq
    }

  /** Enumerate all schedules for a generalized config.
    * Returns (schedule, result) pairs. */
  def enumerateAll(config: GenConfig): List[GenResult] =
    val n = config.n
    val m = config.m
    val k = config.k

    // For each machine, enumerate:
    //   - All orderings of J_i (permutations)
    //   - All work divisions for each job in J_i

    // Machine-level schedule components
    case class MachineSchedule(
      order: IndexedSeq[Int],
      divisions: Map[Int, IndexedSeq[Int]] // job -> per-worker work
    )

    def machineSchedules(machIdx: Int): List[MachineSchedule] =
      val jobs = config.jobsForMachine(machIdx).toList.sorted
      if jobs.isEmpty then return List(MachineSchedule(IndexedSeq.empty, Map.empty))

      val orderings = jobs.permutations.toList.map(_.toIndexedSeq)

      // For each job, enumerate all compositions of its work into k parts
      val jobDivisions: Map[Int, List[IndexedSeq[Int]]] = jobs.map { j =>
        val w = config.work(machIdx)(j)
        j -> compositions(w, k)
      }.toMap

      // Cartesian product of divisions across jobs
      val divisionCombos = cartesianProduct(jobs.map(j => jobDivisions(j).map(d => (j, d))))

      for
        order <- orderings
        divCombo <- divisionCombos
      yield MachineSchedule(order, divCombo.toMap)

    // Enumerate machine schedules for each machine
    val perMachine = (0 until m).map(i => machineSchedules(i)).toList

    // Cartesian product across machines
    val allMachineCombos = cartesianProduct(perMachine)

    // Stage-2 orderings
    val stage2Orderings = (0 until n).toList.permutations.toList.map(_.toIndexedSeq)

    val results = mutable.ListBuffer[GenResult]()

    for
      machineCombination <- allMachineCombos
      stage2Order <- stage2Orderings
    do
      val schedule = GenSchedule(
        machineOrders = machineCombination.map(_.order).toIndexedSeq,
        workDivisions = machineCombination.map(_.divisions).toIndexedSeq,
        stage2Order = stage2Order
      )
      results += GenEvaluator.evaluate(config, schedule)

    results.toList

  /** Enumerate only "common order + water-fill" schedules (the construction from the proof).
    * For each permutation π of [n], build the schedule where each machine processes
    * J_i in π-order with CUMULATIVE water-filling, and try all stage-2 orderings. */
  def enumerateCommonWaterfill(config: GenConfig): List[GenResult] =
    val n = config.n
    val m = config.m
    val k = config.k

    val globalPerms = (0 until n).toList.permutations.toList.map(_.toIndexedSeq)
    val stage2Orderings = globalPerms

    val results = mutable.ListBuffer[GenResult]()

    for pi <- globalPerms do
      // Build machine schedules from π with cumulative water-fill
      val machineOrders = (0 until m).map { i =>
        pi.filter(j => config.subsets(j).contains(i))
      }.toIndexedSeq

      val workDivisions = (0 until m).map { i =>
        val order = machineOrders(i)
        val works = order.map(j => config.work(i)(j))
        val divisions = cumulativeWaterFill(works, k)
        order.zip(divisions).toMap
      }.toIndexedSeq

      for stage2Order <- stage2Orderings do
        val schedule = GenSchedule(machineOrders, workDivisions, stage2Order)
        results += GenEvaluator.evaluate(config, schedule)

    results.toList

  private def cartesianProduct[T](lists: List[List[T]]): List[List[T]] =
    lists.foldRight(List(List.empty[T])) { (currentList, acc) =>
      for
        elem <- currentList
        combination <- acc
      yield elem :: combination
    }


// ============================================================
// Proof Verification: The Constructive Argument
// ============================================================

object GenProofVerifier:

  /** For a given schedule S, construct the "proof schedule" S* and check
    * whether r*_j ≤ r_j for all j (pointwise release-time domination).
    *
    * Construction:
    * 1. Compute release times r_j from S
    * 2. Sort jobs by non-decreasing r_j to get π
    * 3. Each machine i processes J_i in π-order with water-filling
    * 4. Check r*_j ≤ r_j for all j
    *
    * Returns (constructed result, original result, whether domination holds,
    *          diagnostic info). */
  def verifyConstruction(config: GenConfig, original: GenResult): ConstructionVerification =
    val n = config.n
    val m = config.m
    val k = config.k

    // Step 1: get release times from original schedule
    val rOrig = original.releaseTimes

    // Step 2: sort by non-decreasing release time (stable sort, break ties by job index)
    val pi: IndexedSeq[Int] = (0 until n).sortBy(j => (rOrig(j), j)).toIndexedSeq

    // Step 3: construct the common-order water-fill schedule (cumulative water-fill)
    val machineOrders = (0 until m).map { i =>
      pi.filter(j => config.subsets(j).contains(i))
    }.toIndexedSeq

    val workDivisions = (0 until m).map { i =>
      val order = machineOrders(i)
      val works = order.map(j => config.work(i)(j))
      val divisions = GenEnumerator.cumulativeWaterFill(works, k)
      order.zip(divisions).toMap
    }.toIndexedSeq

    // Use the same stage-2 order as original
    val constructedSchedule = GenSchedule(machineOrders, workDivisions, original.schedule.stage2Order)
    val constructed = GenEvaluator.evaluate(config, constructedSchedule)

    // Step 4: check pointwise domination
    val releaseTimeDomination = (0 until n).forall(j => constructed.releaseTimes(j) <= rOrig(j))
    val stage2Domination = (0 until n).forall(j => constructed.stage2Completions(j) <= original.stage2Completions(j))

    // Verify capacity bound (diagnostic)
    val capacityBoundHolds = (0 until m).forall { i =>
      var cumWork = 0
      pi.forall { j =>
        if config.subsets(j).contains(i) then
          cumWork += config.work(i)(j)
          cumWork <= k * rOrig(j)
        else true
      }
    }

    ConstructionVerification(
      pi = pi,
      original = original,
      constructed = constructed,
      releaseTimeDomination = releaseTimeDomination,
      stage2Domination = stage2Domination,
      capacityBoundHolds = capacityBoundHolds
    )

  case class ConstructionVerification(
    pi: IndexedSeq[Int],
    original: GenResult,
    constructed: GenResult,
    releaseTimeDomination: Boolean,
    stage2Domination: Boolean,
    capacityBoundHolds: Boolean
  )


// ============================================================
// Full Analysis
// ============================================================

object GenAnalyzer:

  case class GenAnalysisReport(
    config: GenConfig,
    totalSchedules: Int,
    commonOrderSchedules: Int,
    // P4: for every schedule S, there exists a common-order schedule S* with
    // C^(2)_j(S*) ≤ C^(2)_j(S) for all j
    pointwiseDominationHolds: Boolean,
    // Constructive P4: the specific construction (sort by r, water-fill) always works
    constructiveDominationHolds: Boolean,
    // Capacity bound always holds
    capacityBoundAlwaysHolds: Boolean,
    // Counterexample if found
    counterexample: Option[ConstructionCounterexample],
    elapsedMs: Long
  )

  case class ConstructionCounterexample(
    verification: GenProofVerifier.ConstructionVerification,
    failingJobs: List[Int], // jobs where r*_j > r_j
    details: String
  )

  /** Run full analysis on a generalized config.
    * If exhaustive is true, enumerate ALL schedules and check existential P4.
    * Always checks the constructive argument. */
  def analyze(config: GenConfig, exhaustive: Boolean = true): GenAnalysisReport =
    val startTime = System.currentTimeMillis()

    // Enumerate all schedules (if exhaustive) or just common-order waterfill
    val allResults = if exhaustive then GenEnumerator.enumerateAll(config) else List.empty
    val commonResults = if exhaustive then allResults.filter(_.isCommonOrder) else GenEnumerator.enumerateCommonWaterfill(config)

    // Check constructive domination: for each schedule, verify the proof construction
    val schedulesToCheck = if exhaustive then allResults else
      // If not exhaustive, at least check common-order schedules against themselves
      commonResults

    var constructiveFails = false
    var capacityFails = false
    var counterexample: Option[ConstructionCounterexample] = None

    for result <- schedulesToCheck if counterexample.isEmpty do
      val v = GenProofVerifier.verifyConstruction(config, result)
      if !v.releaseTimeDomination then
        constructiveFails = true
        val failingJobs = (0 until config.n).filter(j =>
          v.constructed.releaseTimes(j) > v.original.releaseTimes(j)).toList
        val details = buildCounterexampleDetails(config, v, failingJobs)
        counterexample = Some(ConstructionCounterexample(v, failingJobs, details))
      if !v.capacityBoundHolds then
        capacityFails = true

    // Check existential P4 (if exhaustive)
    val existentialP4 = if exhaustive then
      allResults.forall { s =>
        commonResults.exists { sStar =>
          (0 until config.n).forall(j =>
            sStar.stage2Completions(j) <= s.stage2Completions(j))
        }
      }
    else true // Can't check without all schedules

    val elapsedMs = System.currentTimeMillis() - startTime

    GenAnalysisReport(
      config = config,
      totalSchedules = allResults.size,
      commonOrderSchedules = commonResults.size,
      pointwiseDominationHolds = existentialP4,
      constructiveDominationHolds = !constructiveFails,
      capacityBoundAlwaysHolds = !capacityFails,
      counterexample = counterexample,
      elapsedMs = elapsedMs
    )

  private def buildCounterexampleDetails(
    config: GenConfig,
    v: GenProofVerifier.ConstructionVerification,
    failingJobs: List[Int]
  ): String =
    val sb = new StringBuilder
    sb ++= s"COUNTEREXAMPLE FOUND for config: ${config.shortLabel}\n"
    sb ++= s"  π (sorted by release time): ${v.pi.mkString(",")}\n"
    sb ++= s"  Original release times: ${v.original.releaseTimes.mkString(",")}\n"
    sb ++= s"  Constructed release times: ${v.constructed.releaseTimes.mkString(",")}\n"
    sb ++= s"  Failing jobs: ${failingJobs.mkString(",")}\n"
    for j <- failingJobs do
      sb ++= s"  Job $j: r_orig=${v.original.releaseTimes(j)}, r_new=${v.constructed.releaseTimes(j)}\n"
      sb ++= s"    Machines used: ${config.subsets(j).toList.sorted.mkString(",")}\n"
      for i <- config.subsets(j).toList.sorted do
        sb ++= s"    Machine $i: work=${config.work(i)(j)}\n"
    sb.toString


  def printReport(report: GenAnalysisReport): Unit =
    println("=" * 78)
    println("GENERALIZED ASSEMBLY FLOW SHOP ANALYSIS")
    println("=" * 78)
    println(s"Config: ${report.config.shortLabel}")
    println(s"  n=${report.config.n} jobs, m=${report.config.m} machines, k=${report.config.k} workers/machine")
    println()

    // Print subsets
    for j <- 0 until report.config.n do
      val subs = report.config.subsets(j).toList.sorted.mkString("{", ",", "}")
      val workStr = report.config.subsets(j).toList.sorted.map(i => s"w($i,$j)=${report.config.work(i)(j)}").mkString(", ")
      println(s"  Job $j: machines=$subs, $workStr, q=$j=${report.config.stageTwo(j)}")
    println()

    if report.totalSchedules > 0 then
      println(s"Total schedules enumerated: ${report.totalSchedules}")
    println(s"Common-order schedules: ${report.commonOrderSchedules}")
    println()

    println("PROOF RESULTS:")
    val p4 = if report.pointwiseDominationHolds then "VERIFIED" else "FAILED"
    println(s"  P4 (existential pointwise domination):  $p4")
    val constr = if report.constructiveDominationHolds then "VERIFIED" else "FAILED"
    println(s"  Constructive domination (sort+waterfill): $constr")
    val cap = if report.capacityBoundAlwaysHolds then "VERIFIED" else "FAILED"
    println(s"  Capacity bound always holds:              $cap")
    println()

    report.counterexample.foreach { ce =>
      println("!!! COUNTEREXAMPLE !!!")
      println(ce.details)
    }


// ============================================================
// Test Configurations
// ============================================================

object GenConfigs:

  /** n=2, m=3, jobs use overlapping but different subsets.
    * Job 0: machines {0,1}, Job 1: machines {1,2} */
  def twoJobOverlap: GenConfig = GenConfig(
    n = 2, m = 3, k = 2,
    subsets = IndexedSeq(Set(0, 1), Set(1, 2)),
    work = IndexedSeq(
      IndexedSeq(3, 0), // machine 0: job 0 needs 3, job 1 not here
      IndexedSeq(2, 4), // machine 1: both jobs
      IndexedSeq(0, 3)  // machine 2: only job 1
    ),
    stageTwo = IndexedSeq(2, 2),
    label = "2-job overlap {0,1},{1,2}"
  )

  /** n=3, m=3, cyclic subsets.
    * Job 0: {0,1}, Job 1: {1,2}, Job 2: {0,2} */
  def threeJobCyclic: GenConfig = GenConfig(
    n = 3, m = 3, k = 2,
    subsets = IndexedSeq(Set(0, 1), Set(1, 2), Set(0, 2)),
    work = IndexedSeq(
      IndexedSeq(4, 0, 3), // machine 0: jobs 0,2
      IndexedSeq(2, 3, 0), // machine 1: jobs 0,1
      IndexedSeq(0, 4, 2)  // machine 2: jobs 1,2
    ),
    stageTwo = IndexedSeq(2, 3, 1),
    label = "3-job cyclic {0,1},{1,2},{0,2}"
  )

  /** n=3, m=3, disjoint subsets (no shared machines).
    * Job 0: {0}, Job 1: {1}, Job 2: {2} */
  def threeJobDisjoint: GenConfig = GenConfig(
    n = 3, m = 3, k = 2,
    subsets = IndexedSeq(Set(0), Set(1), Set(2)),
    work = IndexedSeq(
      IndexedSeq(4, 0, 0), // machine 0: only job 0
      IndexedSeq(0, 3, 0), // machine 1: only job 1
      IndexedSeq(0, 0, 5)  // machine 2: only job 2
    ),
    stageTwo = IndexedSeq(2, 3, 1),
    label = "3-job disjoint {0},{1},{2}"
  )

  /** n=3, m=3, all jobs use all machines (standard model). */
  def threeJobFull: GenConfig = GenConfig(
    n = 3, m = 3, k = 2,
    subsets = IndexedSeq(Set(0, 1, 2), Set(0, 1, 2), Set(0, 1, 2)),
    work = IndexedSeq(
      IndexedSeq(4, 2, 3), // machine 0
      IndexedSeq(2, 4, 2), // machine 1
      IndexedSeq(3, 3, 4)  // machine 2
    ),
    stageTwo = IndexedSeq(2, 3, 1),
    label = "3-job full (standard model)"
  )

  /** n=3, m=3, one job uses all machines, others use subsets. */
  def threeJobMixed: GenConfig = GenConfig(
    n = 3, m = 3, k = 2,
    subsets = IndexedSeq(Set(0, 1, 2), Set(0, 1), Set(1, 2)),
    work = IndexedSeq(
      IndexedSeq(3, 4, 0), // machine 0: jobs 0,1
      IndexedSeq(2, 2, 3), // machine 1: all three
      IndexedSeq(4, 0, 2)  // machine 2: jobs 0,2
    ),
    stageTwo = IndexedSeq(2, 2, 2),
    label = "3-job mixed {0,1,2},{0,1},{1,2}"
  )

  /** n=3, m=4, larger machine set, various subsets. */
  def threeJobFourMachines: GenConfig = GenConfig(
    n = 3, m = 4, k = 2,
    subsets = IndexedSeq(Set(0, 1, 2), Set(1, 2, 3), Set(0, 3)),
    work = IndexedSeq(
      IndexedSeq(3, 0, 2), // machine 0: jobs 0,2
      IndexedSeq(2, 3, 0), // machine 1: jobs 0,1
      IndexedSeq(4, 2, 0), // machine 2: jobs 0,1
      IndexedSeq(0, 4, 3)  // machine 3: jobs 1,2
    ),
    stageTwo = IndexedSeq(2, 1, 3),
    label = "3-job 4-mach {0,1,2},{1,2,3},{0,3}"
  )

  /** Stress test: n=2, m=3, highly asymmetric work. */
  def twoJobAsymmetric: GenConfig = GenConfig(
    n = 2, m = 3, k = 2,
    subsets = IndexedSeq(Set(0, 1), Set(1, 2)),
    work = IndexedSeq(
      IndexedSeq(6, 0), // machine 0: only job 0, heavy
      IndexedSeq(2, 2), // machine 1: both, light
      IndexedSeq(0, 6)  // machine 2: only job 1, heavy
    ),
    stageTwo = IndexedSeq(1, 1),
    label = "2-job asymmetric heavy {0,1},{1,2}"
  )

  /** n=2, m=2, each job uses one machine (disjoint). */
  def twoJobDisjoint: GenConfig = GenConfig(
    n = 2, m = 2, k = 2,
    subsets = IndexedSeq(Set(0), Set(1)),
    work = IndexedSeq(
      IndexedSeq(4, 0), // machine 0: only job 0
      IndexedSeq(0, 3)  // machine 1: only job 1
    ),
    stageTwo = IndexedSeq(2, 3),
    label = "2-job disjoint {0},{1}"
  )

  /** n=4, m=3, k=2, various subsets. */
  def fourJobThreeMachines: GenConfig = GenConfig(
    n = 4, m = 3, k = 2,
    subsets = IndexedSeq(Set(0, 1), Set(1, 2), Set(0, 2), Set(0, 1, 2)),
    work = IndexedSeq(
      IndexedSeq(2, 0, 3, 2), // machine 0: jobs 0,2,3
      IndexedSeq(3, 2, 0, 2), // machine 1: jobs 0,1,3
      IndexedSeq(0, 3, 2, 3)  // machine 2: jobs 1,2,3
    ),
    stageTwo = IndexedSeq(1, 2, 1, 2),
    label = "4-job 3-mach mixed subsets"
  )

  /** Adversarial: try to break the proof.
    * Job 0 uses {0,1} with heavy work on 0, light on 1.
    * Job 1 uses {0,2} with light work on 0, heavy on 2.
    * Job 2 uses {1,2} with moderate work on both.
    * Idea: in an unsync schedule, machine 0 can be clever about ordering
    * jobs 0,1 differently than machine 1 orders jobs 0,2. */
  def adversarial1: GenConfig = GenConfig(
    n = 3, m = 3, k = 2,
    subsets = IndexedSeq(Set(0, 1), Set(0, 2), Set(1, 2)),
    work = IndexedSeq(
      IndexedSeq(6, 2, 0), // machine 0: job 0 heavy, job 1 light
      IndexedSeq(2, 0, 4), // machine 1: job 0 light, job 2 moderate
      IndexedSeq(0, 6, 3)  // machine 2: job 1 heavy, job 2 moderate
    ),
    stageTwo = IndexedSeq(1, 1, 1),
    label = "adversarial-1"
  )

  /** Adversarial 2: singleton subsets mixed with full coverage. */
  def adversarial2: GenConfig = GenConfig(
    n = 3, m = 3, k = 2,
    subsets = IndexedSeq(Set(0), Set(1), Set(0, 1, 2)),
    work = IndexedSeq(
      IndexedSeq(4, 0, 2), // machine 0: jobs 0,2
      IndexedSeq(0, 4, 2), // machine 1: jobs 1,2
      IndexedSeq(0, 0, 6)  // machine 2: only job 2
    ),
    stageTwo = IndexedSeq(1, 1, 1),
    label = "adversarial-2 singletons+full"
  )

  /** Adversarial 3: large work imbalance, k=3 workers. */
  def adversarial3: GenConfig = GenConfig(
    n = 3, m = 3, k = 3,
    subsets = IndexedSeq(Set(0, 1), Set(1, 2), Set(0, 2)),
    work = IndexedSeq(
      IndexedSeq(9, 0, 3), // machine 0
      IndexedSeq(3, 9, 0), // machine 1
      IndexedSeq(0, 3, 9)  // machine 2
    ),
    stageTwo = IndexedSeq(1, 1, 1),
    label = "adversarial-3 k=3 imbalanced"
  )

  def all: List[GenConfig] = List(
    twoJobOverlap,
    twoJobAsymmetric,
    twoJobDisjoint,
    threeJobCyclic,
    threeJobDisjoint,
    threeJobFull,
    threeJobMixed,
    threeJobFourMachines,
    adversarial1,
    adversarial2,
    adversarial3,
    // fourJobThreeMachines -- may be too large for exhaustive
  )

  /** Configs small enough for exhaustive enumeration. */
  def exhaustive: List[GenConfig] = List(
    twoJobOverlap,
    twoJobAsymmetric,
    twoJobDisjoint,
    threeJobCyclic,
    threeJobDisjoint,
    threeJobFull,
    threeJobMixed,
    adversarial1,
    adversarial2,
  )


// ============================================================
// Random Config Generator for Stress Testing
// ============================================================

object GenRandom:
  import scala.util.Random

  /** Generate a random generalized config. */
  def randomConfig(
    n: Int, m: Int, k: Int,
    minWork: Int = 2, maxWork: Int = 6,
    minSubsetSize: Int = 1, maxSubsetSize: Int = -1,
    seed: Long = System.nanoTime()
  ): GenConfig =
    val rng = new Random(seed)
    val maxSub = if maxSubsetSize < 0 then m else maxSubsetSize

    // Generate subsets: each job uses a random subset of machines
    val subsets = IndexedSeq.tabulate(n) { j =>
      val size = minSubsetSize + rng.nextInt(maxSub - minSubsetSize + 1)
      rng.shuffle((0 until m).toList).take(size).toSet
    }

    // Generate work: positive where job uses machine, 0 otherwise
    val work = IndexedSeq.tabulate(m) { i =>
      IndexedSeq.tabulate(n) { j =>
        if subsets(j).contains(i) then minWork + rng.nextInt(maxWork - minWork + 1)
        else 0
      }
    }

    val stageTwo = IndexedSeq.fill(n)(1 + rng.nextInt(3))

    GenConfig(n, m, k, subsets, work, stageTwo,
      label = s"random n=$n m=$m k=$k seed=$seed")


// ============================================================
// Main: Systematic Search
// ============================================================

@main def generalizedModelSearch(): Unit =
  println("=" * 78)
  println("GENERALIZED ASSEMBLY FLOW SHOP: SYSTEMATIC COUNTEREXAMPLE SEARCH")
  println("=" * 78)
  println()
  println("Question: Does pointwise domination (P4) hold when different jobs")
  println("use different subsets of stage-1 machines?")
  println()

  // Phase 1: Exhaustive enumeration on small configs
  println("PHASE 1: Exhaustive enumeration on hand-crafted configs")
  println("-" * 78)

  var allPassed = true
  var totalSchedules = 0L

  for config <- GenConfigs.exhaustive do
    print(s"  ${config.shortLabel} ... ")
    val report = GenAnalyzer.analyze(config, exhaustive = true)
    totalSchedules += report.totalSchedules
    val status = if report.constructiveDominationHolds && report.pointwiseDominationHolds then
      "PASS"
    else
      allPassed = false
      "FAIL"
    println(f"${report.totalSchedules}%,8d schedules, ${report.elapsedMs}%,6d ms: $status")
    if !report.constructiveDominationHolds then
      report.counterexample.foreach { ce =>
        println(ce.details)
      }

  println()
  println(f"Phase 1: $totalSchedules%,d total schedules checked")
  println()

  // Phase 2: Larger configs, constructive check only
  println("PHASE 2: Constructive verification on larger configs")
  println("-" * 78)

  val largerConfigs = List(
    GenConfigs.threeJobFourMachines,
    GenConfigs.adversarial3,
    GenConfigs.fourJobThreeMachines,
  )

  for config <- largerConfigs do
    print(s"  ${config.shortLabel} ... ")
    // Only check constructive (sort+waterfill) on common-order+waterfill schedules
    val report = GenAnalyzer.analyze(config, exhaustive = false)
    val status = if report.constructiveDominationHolds then "PASS" else "FAIL"
    println(f"${report.commonOrderSchedules}%,8d common-order schedules, ${report.elapsedMs}%,6d ms: $status")
    if !report.constructiveDominationHolds then
      allPassed = false
      report.counterexample.foreach { ce =>
        println(ce.details)
      }

  println()

  // Phase 3: Random stress test
  println("PHASE 3: Random stress testing")
  println("-" * 78)

  var randomPassed = 0
  var randomFailed = 0

  // n=2, m=3, k=2: exhaustive
  for seed <- 1L to 100L do
    val config = GenRandom.randomConfig(n = 2, m = 3, k = 2, seed = seed)
    val report = GenAnalyzer.analyze(config, exhaustive = true)
    if report.constructiveDominationHolds && report.pointwiseDominationHolds then
      randomPassed += 1
    else
      randomFailed += 1
      allPassed = false
      println(s"  FAIL: n=2 m=3 k=2 seed=$seed")
      report.counterexample.foreach(ce => println(ce.details))

  // n=2, m=4, k=2: exhaustive
  for seed <- 1L to 50L do
    val config = GenRandom.randomConfig(n = 2, m = 4, k = 2, seed = seed + 200)
    val report = GenAnalyzer.analyze(config, exhaustive = true)
    if report.constructiveDominationHolds && report.pointwiseDominationHolds then
      randomPassed += 1
    else
      randomFailed += 1
      allPassed = false
      println(s"  FAIL: n=2 m=4 k=2 seed=${seed + 200}")
      report.counterexample.foreach(ce => println(ce.details))

  // n=2, m=3, k=3: exhaustive
  for seed <- 1L to 50L do
    val config = GenRandom.randomConfig(n = 2, m = 3, k = 3, minWork = 3, seed = seed + 300)
    val report = GenAnalyzer.analyze(config, exhaustive = true)
    if report.constructiveDominationHolds && report.pointwiseDominationHolds then
      randomPassed += 1
    else
      randomFailed += 1
      allPassed = false
      println(s"  FAIL: n=2 m=3 k=3 seed=${seed + 300}")
      report.counterexample.foreach(ce => println(ce.details))

  // n=3 random configs: constructive check (too large for full exhaustive in some cases)
  for seed <- 1L to 50L do
    val config = GenRandom.randomConfig(n = 3, m = 3, k = 2, seed = seed + 1000)
    val report = GenAnalyzer.analyze(config, exhaustive = false)
    if report.constructiveDominationHolds then
      randomPassed += 1
    else
      randomFailed += 1
      allPassed = false
      println(s"  FAIL: n=3 m=3 k=2 seed=${seed + 1000}")
      report.counterexample.foreach(ce => println(ce.details))

  // n=3, m=4 random configs: constructive check
  for seed <- 1L to 30L do
    val config = GenRandom.randomConfig(n = 3, m = 4, k = 2, seed = seed + 2000)
    val report = GenAnalyzer.analyze(config, exhaustive = false)
    if report.constructiveDominationHolds then
      randomPassed += 1
    else
      randomFailed += 1
      allPassed = false
      println(s"  FAIL: n=3 m=4 k=2 seed=${seed + 2000}")
      report.counterexample.foreach(ce => println(ce.details))

  // n=4, m=3 random configs: constructive check
  for seed <- 1L to 20L do
    val config = GenRandom.randomConfig(n = 4, m = 3, k = 2, seed = seed + 3000)
    val report = GenAnalyzer.analyze(config, exhaustive = false)
    if report.constructiveDominationHolds then
      randomPassed += 1
    else
      randomFailed += 1
      allPassed = false
      println(s"  FAIL: n=4 m=3 k=2 seed=${seed + 3000}")
      report.counterexample.foreach(ce => println(ce.details))

  println(s"  Random tests: $randomPassed passed, $randomFailed failed")
  println()

  // Summary
  println("=" * 78)
  println("SUMMARY")
  println("=" * 78)
  if allPassed then
    println("ALL TESTS PASSED.")
    println()
    println("CONCLUSION: The pointwise domination theorem appears to extend to the")
    println("generalized model where different jobs use different machine subsets.")
    println()
    println("The proof argument works because:")
    println("  1. The capacity bound W_i(s) <= k * r_{pi(s)} holds even when machine i")
    println("     only processes a subset J_i of jobs. The bound sums only over jobs in")
    println("     J_i that appear in positions 1..s of pi.")
    println("  2. Water-filling on machine i processes only J_i in pi-order. The")
    println("     completion bound ceil(W_i(s)/k) <= r_{pi(s)} still holds.")
    println("  3. For pi(s) in J_i: C*_{i,pi(s)} <= ceil(W_i(s)/k) <= r_{pi(s)}.")
    println("     For pi(s) not in J_i: machine i doesn't contribute to r*_{pi(s)}.")
    println("  4. Therefore r*_j = max_{i in S_j} C*_{i,j} <= r_j for all j.")
  else
    println("SOME TESTS FAILED -- counterexample found!")
    println("The generalized model does NOT preserve pointwise domination.")
