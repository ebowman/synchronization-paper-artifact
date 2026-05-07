/**
 * Test whether concordant work profiles (same relative ordering of jobs
 * at every stage) guarantee chain dominance for makespan and WCT.
 */
object ConcordantTest:

  def isConcordant(config: ChainConfig): Boolean =
    val n = config.numJobs
    val L = config.numStages
    // For each pair of jobs, check if their relative ordering is the same at every stage
    (0 until n).combinations(2).forall { pair =>
      val i = pair(0); val j = pair(1)
      val signs = (0 until L).map { s =>
        val wi = config.workPerStage(s)(i)
        val wj = config.workPerStage(s)(j)
        if wi > wj then 1 else if wi < wj then -1 else 0
      }.filter(_ != 0) // ignore ties
      // Concordant: all non-zero signs are the same
      signs.distinct.size <= 1
    }

  def main(args: Array[String]): Unit =
    println("Concordant Work Profile Conjecture Test")
    println("=" * 70)

    // Test L=3, n=2, k=2, work 1..6
    var concordantTotal = 0
    var concordantP5Fails = 0
    var concordantP6Fails = 0
    var discordantTotal = 0
    var discordantP5Fails = 0
    var discordantP6Fails = 0

    for {
      k <- List(2)
      w00 <- 1 to 6; w01 <- 1 to 6
      w10 <- 1 to 6; w11 <- 1 to 6
      w20 <- 1 to 6; w21 <- 1 to 6
    } {
      val config = ChainConfig(3, List(List(w00,w01),List(w10,w11),List(w20,w21)),
        List(k,k,k), "")
      val r = ConjectureSearch.analyzeQuick(config)
      if (isConcordant(config)) {
        concordantTotal += 1
        if (!r.p5Holds) concordantP5Fails += 1
        if (!r.p6Holds) concordantP6Fails += 1
      } else {
        discordantTotal += 1
        if (!r.p5Holds) discordantP5Fails += 1
        if (!r.p6Holds) discordantP6Fails += 1
      }
    }

    println(f"\nL=3, n=2, k=2, work 1..6:")
    println(f"  Concordant:  $concordantTotal%6d configs, P5 fails=$concordantP5Fails, P6 fails=$concordantP6Fails")
    println(f"  Discordant:  $discordantTotal%6d configs, P5 fails=$discordantP5Fails, P6 fails=$discordantP6Fails")

    // Also L=2 (to check WCT)
    var c2Total = 0; var c2P6 = 0; var d2Total = 0; var d2P6 = 0
    for {
      w00 <- 1 to 8; w01 <- 1 to 8
      w10 <- 1 to 8; w11 <- 1 to 8
    } {
      val config = ChainConfig(2, List(List(w00,w01),List(w10,w11)), List(2,2), "")
      val r = ConjectureSearch.analyzeQuick(config)
      if (isConcordant(config)) { c2Total += 1; if (!r.p6Holds) c2P6 += 1 }
      else { d2Total += 1; if (!r.p6Holds) d2P6 += 1 }
    }
    println(f"\nL=2, n=2, k=2, work 1..8:")
    println(f"  Concordant:  $c2Total%6d configs, P6 fails=$c2P6")
    println(f"  Discordant:  $d2Total%6d configs, P6 fails=$d2P6")

    // L=3, n=3 concordant check
    var c3Total = 0; var c3P5 = 0; var c3P6 = 0
    var d3Total = 0; var d3P5 = 0; var d3P6 = 0
    for {
      w00 <- 1 to 3; w01 <- 1 to 3; w02 <- 1 to 3
      w10 <- 1 to 3; w11 <- 1 to 3; w12 <- 1 to 3
      w20 <- 1 to 3; w21 <- 1 to 3; w22 <- 1 to 3
    } {
      val config = ChainConfig(3,
        List(List(w00,w01,w02),List(w10,w11,w12),List(w20,w21,w22)),
        List(2,2,2), "")
      val r = ConjectureSearch.analyzeQuick(config)
      if (isConcordant(config)) { c3Total += 1; if (!r.p5Holds) c3P5 += 1; if (!r.p6Holds) c3P6 += 1 }
      else { d3Total += 1; if (!r.p5Holds) d3P5 += 1; if (!r.p6Holds) d3P6 += 1 }
    }
    println(f"\nL=3, n=3, k=2, work 1..3:")
    println(f"  Concordant:  $c3Total%6d configs, P5=$c3P5, P6=$c3P6")
    println(f"  Discordant:  $d3Total%6d configs, P5=$d3P5, P6=$d3P6")
