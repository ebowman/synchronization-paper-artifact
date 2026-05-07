import scala.concurrent.{Future, Await, ExecutionContext}
import scala.concurrent.duration.*

object Main:

  def main(args: Array[String]): Unit =
    val mode = if args.nonEmpty then args(0) else "quick"
    val maxSchedules = if args.length > 1 then args(1).toLong else 10_000_000L

    val configs: List[SweepConfig] = mode match
      case "baseline" => List(StandardConfigs.baseline)
      case "quick"    => StandardConfigs.quick
      case "sym"      => StandardConfigs.symmetric
      case "asym"     => StandardConfigs.asymmetric
      case "val"      => StandardConfigs.valueWeighted
      case "hetero"   => StandardConfigs.heterogeneous
      case "full"     => StandardConfigs.full
      case "wip"      =>
        println("WIP Analysis Mode")
        println()
        val allConfigs = StandardConfigs.full
        val comparisons = WIPAnalysis.analyze(allConfigs, maxSchedules)
        WIPAnalysis.printReport(comparisons)
        return
      case "revenue"  =>
        println("Revenue Impact Analysis Mode")
        println()
        val allConfigs = StandardConfigs.full
        val comparisons = RevenueAnalysis.analyze(allConfigs, maxSchedules)
        RevenueAnalysis.printReport(comparisons)
        return
      case "chain" =>
        println("L-Stage Chain Scheduling Analysis")
        println()
        val passed = ChainRunner.runAll(StandardChainConfigs.all)
        if !passed then sys.exit(1)
        return
      case "robust" =>
        println("Robustness Simulation (Four-Tier Comparison)")
        println()
        val seed = if args.length > 1 then args(1).toLong else 42L
        RobustnessSimulation.main(Array(seed.toString))
        return
      case "dag" =>
        println("DAG Dependency Scheduling Analysis")
        println()
        val handcraftedPass = DAGRunner.runAll(StandardDAGConfigs.allSmall)
        val randomN2Pass = DAGRunner.runRandomStress(numTrials = 50, n = 2, seed = 42L)
        val diamondN3Pass = DAGRunner.diamondStressN3(numTrials = 20, maxWork = 5, seed = 123L)
        if !(handcraftedPass && randomN2Pass && diamondN3Pass) then sys.exit(1)
        return
      case "dag-verify" =>
        println("DAG Paper Verification (reproducing exact paper claims)")
        println()
        val passed = DAGPaperVerification.runAll(verbose = true)
        if !passed then sys.exit(1)
        return
      case other =>
        println(s"Unknown mode: $other. Use: baseline | quick | sym | asym | val | full | wip | chain | robust | dag | dag-verify")
        sys.exit(1)

    println(s"Mode: $mode  (${configs.size} configuration(s), max schedules: ${maxSchedules})")
    println()

    val summary = ConfigSweep.runAll(configs, verbose = true, maxSchedules = maxSchedules)
    ConfigSweep.printSummaryTable(summary)

    // Print detailed report only for baseline or single-config runs
    if configs.size == 1 then
      ConfigSweep.printDetailedResult(summary.results.head)

    // Exit with non-zero if any proof condition failed
    if !summary.allVerified then sys.exit(1)


// --- Parallel Runner (JVM-only, uses thread pools and Await) ---

object ParallelConfigSweep:

  /** Run all configurations in parallel using a thread pool. */
  def runAllParallel(
    configs: List[SweepConfig],
    verbose: Boolean = false,
    maxSchedules: Long = ConfigRunner.DefaultMaxSchedules
  ): SweepSummary =
    val pool = java.util.concurrent.Executors.newFixedThreadPool(
      Runtime.getRuntime.availableProcessors()
    )
    given ExecutionContext = ExecutionContext.fromExecutorService(pool)

    try
      val futures = configs.zipWithIndex.map { (config, idx) =>
        Future {
          if verbose then
            synchronized { println(s"[${idx + 1}/${configs.size}] Running: ${config.shortLabel} ...") }

          val result = ConfigRunner.run(config, maxSchedules)

          if verbose then
            if result.skipped then
              synchronized { println(s"  -> SKIPPED: ${result.skipReason}") }
            else
              val status = if ConfigSweep.allConditionsVerified(result.report) then "ALL VERIFIED" else "SOME FAILED"
              synchronized {
                println(f"  -> ${result.scheduleCount}%,d schedules in ${result.elapsedMs}%,d ms: $status")
              }

          result
        }
      }

      val results = Await.result(Future.sequence(futures), 30.minutes)
      val allOk = results.filterNot(_.skipped).forall(r => ConfigSweep.allConditionsVerified(r.report))
      SweepSummary(results.toList, allOk)
    finally
      pool.shutdown()
