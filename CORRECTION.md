# Correction notice (June 2026)

The manuscript archived in this record (`paper/synchronization.tex`,
"Permutation-Schedule Dominance for Two-Stage Assembly Flow Shops with
Divisible Work", extended version) contains a conjecture and an
associated empirical claim that are hereby corrected.

**What is corrected.** The "Dominance landscape" table and the
accompanying text conjectured that makespan dominance of permutation
(fully synchronized) schedules extends to diamond
(S → {A,B} → T) and fork-join–fork-join ({A,B} → C → {D,E} → F)
topologies, supported by a reported 2×10⁷+ verified instances with
zero failures.

**The correction.** The conjecture is false. Counterexamples exist in
both topologies (e.g., diamond with works A(1,2) | B(4,1) | C(1,1) |
D(1,2), k=2: best synchronized makespan 4.0 versus optimum 3.5), and
failures are not rare once source-stage works vary (0.55% of all
diamond instances with works ≤ 4; ~5% at n=3 with works ≤ 8). The
earlier evidence had two blind spots: the exhaustive sweeps varied
works only at non-source stages, and the random n=3 sweep diluted over
a 12-dimensional work cube. In addition, the reported zero-failure
random sweep does not reproduce: rerunning the archived generator with
its original seed yields dominance failures within 200,000 instances.
That empirical claim is withdrawn.

**The replacement result.** A complete characterization now stands in
place of the conjecture: permutation schedules are makespan-optimal at
every sink for every work assignment **if and only if** the dependency
DAG contains no directed path through three stages. The
characterization, its proofs, the counterexample families, and policy
benchmarks appear in the companion paper

> Bowman, E. (2026). *The Boundary of Synchronization Dominance: A
> Depth Characterization for Divisible-Work Scheduling on DAGs.*
> (companion to the paper archived here; prepared for submission to
> the Journal of Scheduling).

All counterexamples and statistics are reproducible from the test
suites in the `prioritizer` repository
(https://github.com/ebowman/prioritizer): `DiamondCETest`,
`DAGBoundaryProbes`, `DAGBoundaryProbes2`, `DAGGapNumbers`.

The two-stage assembly results of the archived manuscript — the
pointwise dominance theorem, its Lean 4 formalization, and the L=2
chain results — are unaffected by this correction.
