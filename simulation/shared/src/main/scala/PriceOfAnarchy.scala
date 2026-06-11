/**
 * Price-of-local-ordering analysis ("price of anarchy" for uncoordinated teams).
 *
 * Papers A/B prove the shared (synchronized) ordering is never worse. This module
 * quantifies the converse: how much DO uncoordinated per-team orderings cost?
 *
 * For each configuration we compare, per objective (Cmax, total flowtime, WCT):
 *   - bestSync:  the rules-following outcome (min over synchronized schedules)
 *   - unsync population: mean (a random uncoordinated org) and worst (an unlucky one)
 *   - fraction of unsync schedules strictly worse than the rules-following outcome (bestSync)
 *
 * To control for the work-split confound (bestSync also optimizes splits), we
 * additionally compare WITHIN each work-distribution class that contains both
 * synchronized and unsynchronized schedules: there the only difference between
 * the two populations is the ordering decision itself.
 */

case class ObjectivePrice(
  bestSync: Double,
  worstSync: Double,
  meanSync: Double,
  meanUnsync: Double,
  worstUnsync: Double,
  /** Fraction of unsync schedules strictly worse than the rules-following outcome (bestSync).
    * The complement is the chance uncoordinated teams accidentally match the rules. */
  fracUnsyncWorseThanBestSync: Double
):
  /** Mean relative delay of a random uncoordinated schedule vs following the rules. */
  def meanPrice: Double = meanUnsync / bestSync - 1.0
  /** Worst relative delay vs following the rules. */
  def worstPrice: Double = worstUnsync / bestSync - 1.0

case class ControlledPrice(
  mixedClassCount: Int,
  /** Mean over mixed work-distribution classes of (meanUnsyncInClass / meanSyncInClass - 1). */
  meanGap: Double,
  /** Max over mixed classes of (worstUnsyncInClass / bestSyncInClass - 1). */
  worstGap: Double
)

/** Unsync population split by downstream discipline: does the dependent team
  * pull in FIFO-by-availability order, or re-litigate with its own order?
  * Theory (PoA-2): FIFO downstream caps the makespan price at ~(2 - 1/m);
  * adversarial downstream pushes it to 2W/(W + w_max). Prices vs bestSync. */
case class DownstreamSplit(
  fifoCount: Int,
  advCount: Int,
  fifoMeanCmaxPrice: Double,
  fifoWorstCmaxPrice: Double,
  advMeanCmaxPrice: Double,
  advWorstCmaxPrice: Double,
  fifoWorstFlowPrice: Double,
  advWorstFlowPrice: Double
)

case class ConfigPriceResult(
  config: SweepConfig,
  scheduleCount: Int,
  syncCount: Int,
  unsyncCount: Int,
  makespan: ObjectivePrice,
  flowtime: ObjectivePrice,
  wct: ObjectivePrice,
  controlledMakespan: ControlledPrice,
  controlledFlowtime: ControlledPrice,
  controlledWct: ControlledPrice,
  downstreamSplit: DownstreamSplit = DownstreamSplit(0, 0, 0, 0, 0, 0, 0, 0),
  skipped: Boolean = false,
  skipReason: String = ""
)

object PriceOfAnarchy:

  private def mean(xs: List[Double]): Double =
    if xs.isEmpty then 0.0 else xs.sum / xs.size

  private def objectivePrice(
    sync: List[Double],
    unsync: List[Double]
  ): ObjectivePrice =
    val bestSync = sync.min
    ObjectivePrice(
      bestSync = bestSync,
      worstSync = sync.max,
      meanSync = mean(sync),
      meanUnsync = mean(unsync),
      worstUnsync = unsync.max,
      fracUnsyncWorseThanBestSync = unsync.count(_ > bestSync).toDouble / unsync.size
    )

  private def controlledPrice(
    results: List[ScheduleResult],
    extract: ScheduleResult => Double
  ): ControlledPrice =
    val mixed = results.groupBy(_.workDistributionKey).values.toList
      .map { group =>
        val sync = group.filter(_.classification == ScheduleClass.Synchronized).map(extract)
        val unsync = group.filter(_.classification == ScheduleClass.Unsynchronized).map(extract)
        (sync, unsync)
      }
      .filter((s, u) => s.nonEmpty && u.nonEmpty)
    if mixed.isEmpty then ControlledPrice(0, 0.0, 0.0)
    else
      val gaps = mixed.map((s, u) => mean(u) / mean(s) - 1.0)
      val worstGaps = mixed.map((s, u) => u.max / s.min - 1.0)
      ControlledPrice(mixed.size, mean(gaps), worstGaps.max)

  /** True iff the dependent team processes initiatives in non-decreasing order
    * of their stage-1 availability (FIFO-by-availability; ties any order). */
  private def isFifoDownstream(combined: List[TeamSchedule]): Boolean =
    val foundation = combined.filter(_.team.teamType == Foundation)
    val availByName: Map[String, Int] =
      WorkDivisionGenerator.computeInitiativeCompletionTimes(foundation)
        .map((init, t) => init.name -> t)
    val depOrder = combined.filter(_.team.teamType == Dependent)
      .flatMap(ScheduleClassifier.initiativeOrder(_))
    val avails = depOrder.map(availByName)
    avails.zip(avails.drop(1)).forall((a, b) => a <= b)

  private def downstreamSplit(
    sync: List[ScheduleResult],
    unsync: List[ScheduleResult]
  ): DownstreamSplit =
    val bestSyncCmax = sync.map(_.makespan).min.toDouble
    val bestSyncFlow = sync.map(_.totalFlowTime).min.toDouble
    val (fifo, adv) = unsync.partition(r => isFifoDownstream(r.combined))
    def price(xs: List[ScheduleResult], f: ScheduleResult => Double, base: Double, worst: Boolean): Double =
      if xs.isEmpty then 0.0
      else
        val vals = xs.map(f)
        (if worst then vals.max else mean(vals)) / base - 1.0
    DownstreamSplit(
      fifoCount = fifo.size,
      advCount = adv.size,
      fifoMeanCmaxPrice = price(fifo, _.makespan.toDouble, bestSyncCmax, worst = false),
      fifoWorstCmaxPrice = price(fifo, _.makespan.toDouble, bestSyncCmax, worst = true),
      advMeanCmaxPrice = price(adv, _.makespan.toDouble, bestSyncCmax, worst = false),
      advWorstCmaxPrice = price(adv, _.makespan.toDouble, bestSyncCmax, worst = true),
      fifoWorstFlowPrice = price(fifo, _.totalFlowTime.toDouble, bestSyncFlow, worst = true),
      advWorstFlowPrice = price(adv, _.totalFlowTime.toDouble, bestSyncFlow, worst = true)
    )

  def analyzeConfig(config: SweepConfig, maxSchedules: Long): ConfigPriceResult =
    val sweep = ConfigRunner.run(config, maxSchedules)
    sweep.report match
      case None =>
        ConfigPriceResult(config, 0, 0, 0,
          ObjectivePrice(0, 0, 0, 0, 0, 0), ObjectivePrice(0, 0, 0, 0, 0, 0), ObjectivePrice(0, 0, 0, 0, 0, 0),
          ControlledPrice(0, 0, 0), ControlledPrice(0, 0, 0), ControlledPrice(0, 0, 0),
          skipped = true, skipReason = sweep.skipReason)
      case Some(report) =>
        val results = report.allResults
        val sync = results.filter(_.classification == ScheduleClass.Synchronized)
        val unsync = results.filter(_.classification == ScheduleClass.Unsynchronized)
        if sync.isEmpty || unsync.isEmpty then
          ConfigPriceResult(config, results.size, sync.size, unsync.size,
            ObjectivePrice(0, 0, 0, 0, 0, 0), ObjectivePrice(0, 0, 0, 0, 0, 0), ObjectivePrice(0, 0, 0, 0, 0, 0),
            ControlledPrice(0, 0, 0), ControlledPrice(0, 0, 0), ControlledPrice(0, 0, 0),
            skipped = true, skipReason = "no mixed sync/unsync population")
        else
          ConfigPriceResult(
            config = config,
            scheduleCount = results.size,
            syncCount = sync.size,
            unsyncCount = unsync.size,
            makespan = objectivePrice(sync.map(_.makespan.toDouble), unsync.map(_.makespan.toDouble)),
            flowtime = objectivePrice(sync.map(_.totalFlowTime.toDouble), unsync.map(_.totalFlowTime.toDouble)),
            wct = objectivePrice(sync.map(_.weightedCompletionTime), unsync.map(_.weightedCompletionTime)),
            controlledMakespan = controlledPrice(results, _.makespan.toDouble),
            controlledFlowtime = controlledPrice(results, _.totalFlowTime.toDouble),
            controlledWct = controlledPrice(results, _.weightedCompletionTime),
            downstreamSplit = downstreamSplit(sync, unsync)
          )

  def analyze(configs: List[SweepConfig], maxSchedules: Long): List[ConfigPriceResult] =
    configs.zipWithIndex.map { (config, idx) =>
      println(s"[${idx + 1}/${configs.size}] ${config.shortLabel} ...")
      val r = analyzeConfig(config, maxSchedules)
      if r.skipped then println(s"  -> SKIPPED: ${r.skipReason}")
      else println(f"  -> ${r.scheduleCount}%,d schedules (${r.syncCount}%,d sync, ${r.unsyncCount}%,d unsync)")
      r
    }

  private def pct(x: Double): String = f"${x * 100}%6.1f%%"

  def printReport(results: List[ConfigPriceResult]): Unit =
    val ran = results.filterNot(_.skipped)

    println()
    println("=" * 130)
    println("PRICE OF LOCAL ORDERING (uncoordinated per-team orderings vs the shared synchronized order)")
    println("=" * 130)
    println()
    println("Per config, per objective: mean = E[unsync]/bestSync - 1,  worst = max[unsync]/bestSync - 1,")
    println("P(>rules) = fraction of unsync schedules strictly worse than the rules-following outcome (bestSync).")
    println()

    val hdr = f"${"Config"}%-34s | ${"#Unsync"}%8s | ${"Cmax mean"}%9s ${"worst"}%7s ${"P(>rules)"}%8s | ${"Flow mean"}%9s ${"worst"}%7s ${"P(>rules)"}%8s | ${"WCT mean"}%9s ${"worst"}%7s ${"P(>rules)"}%8s"
    println(hdr)
    println("-" * 130)
    for r <- ran do
      println(f"${r.config.shortLabel.take(34)}%-34s | ${r.unsyncCount}%,8d | " +
        f"${pct(r.makespan.meanPrice)}%9s ${pct(r.makespan.worstPrice)}%7s ${pct(r.makespan.fracUnsyncWorseThanBestSync)}%8s | " +
        f"${pct(r.flowtime.meanPrice)}%9s ${pct(r.flowtime.worstPrice)}%7s ${pct(r.flowtime.fracUnsyncWorseThanBestSync)}%8s | " +
        f"${pct(r.wct.meanPrice)}%9s ${pct(r.wct.worstPrice)}%7s ${pct(r.wct.fracUnsyncWorseThanBestSync)}%8s")
    println()

    println("--- Controlled comparison (within work-distribution classes: same splits, only the ordering differs) ---")
    println()
    val hdr2 = f"${"Config"}%-34s | ${"#Mixed"}%6s | ${"Cmax mean"}%9s ${"worst"}%7s | ${"Flow mean"}%9s ${"worst"}%7s | ${"WCT mean"}%9s ${"worst"}%7s"
    println(hdr2)
    println("-" * 110)
    for r <- ran do
      println(f"${r.config.shortLabel.take(34)}%-34s | ${r.controlledMakespan.mixedClassCount}%6d | " +
        f"${pct(r.controlledMakespan.meanGap)}%9s ${pct(r.controlledMakespan.worstGap)}%7s | " +
        f"${pct(r.controlledFlowtime.meanGap)}%9s ${pct(r.controlledFlowtime.worstGap)}%7s | " +
        f"${pct(r.controlledWct.meanGap)}%9s ${pct(r.controlledWct.worstGap)}%7s")
    println()

    println("--- Downstream discipline split (unsync only): FIFO-by-availability vs re-litigated dependent order ---")
    println("    PoA-2 prediction: FIFO downstream caps worst Cmax price near (2-1/m); adversarial downstream reaches 2W/(W+w_max).")
    println()
    val hdr3 = f"${"Config"}%-34s | ${"#FIFO"}%7s ${"#Adv"}%8s | ${"FIFO Cmax mean"}%14s ${"worst"}%7s | ${"Adv Cmax mean"}%13s ${"worst"}%7s | ${"FIFO Flow worst"}%15s ${"Adv Flow worst"}%14s"
    println(hdr3)
    println("-" * 130)
    for r <- ran do
      val d = r.downstreamSplit
      println(f"${r.config.shortLabel.take(34)}%-34s | ${d.fifoCount}%,7d ${d.advCount}%,8d | " +
        f"${pct(d.fifoMeanCmaxPrice)}%14s ${pct(d.fifoWorstCmaxPrice)}%7s | " +
        f"${pct(d.advMeanCmaxPrice)}%13s ${pct(d.advWorstCmaxPrice)}%7s | " +
        f"${pct(d.fifoWorstFlowPrice)}%15s ${pct(d.advWorstFlowPrice)}%14s")
    println()

    // Aggregate summary
    println("=" * 130)
    println("AGGREGATE SUMMARY (across all configurations with mixed populations)")
    println("=" * 130)
    def summarize(name: String, f: ConfigPriceResult => ObjectivePrice): Unit =
      val meanPrices = ran.map(r => f(r).meanPrice)
      val worstPrices = ran.map(r => f(r).worstPrice)
      val probs = ran.map(r => f(r).fracUnsyncWorseThanBestSync)
      println(f"$name%-28s mean price: avg=${pct(mean(meanPrices))}%s  min=${pct(meanPrices.min)}%s  max=${pct(meanPrices.max)}%s   " +
        f"worst price: avg=${pct(mean(worstPrices))}%s  max=${pct(worstPrices.max)}%s   P(>rules): avg=${pct(mean(probs))}%s")
    summarize("Makespan (Cmax)", _.makespan)
    summarize("Total flowtime", _.flowtime)
    summarize("Weighted completion time", _.wct)
    println()
    def summarizeControlled(name: String, f: ConfigPriceResult => ControlledPrice): Unit =
      val withMixed = ran.filter(r => f(r).mixedClassCount > 0)
      val meanGaps = withMixed.map(r => f(r).meanGap)
      val worstGaps = withMixed.map(r => f(r).worstGap)
      println(f"$name%-28s controlled mean gap: avg=${pct(mean(meanGaps))}%s  max=${pct(meanGaps.max)}%s   " +
        f"controlled worst gap: max=${pct(worstGaps.max)}%s")
    summarizeControlled("Makespan (Cmax)", _.controlledMakespan)
    summarizeControlled("Total flowtime", _.controlledFlowtime)
    summarizeControlled("Weighted completion time", _.controlledWct)
    println()
