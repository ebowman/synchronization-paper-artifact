/-
  L-Stage Chain Dominance under Preemptive Priority
  ==================================================

  We formalize the chain dominance theorem:

  **Theorem (Chain Dominance under Preemptive Priority):**
  For any L-stage chain and any schedule S, there exists a
  preemptive priority schedule P with a single permutation π
  such that C_L^P(π(i)) ≤ C_L^S(π(i)) for every job.

  The proof is by induction on L:
  - Base case (L=1): Capacity bound + water-filling from WaterFilling.lean
  - Inductive step: Sort by C_{L-1}^S, apply induction to stages 1..L-1,
    then use priority-order completion and monotonicity at stage L.

  Key lemma: under preemptive priority with ordering π, jobs complete
  each stage in order: C_ℓ^P(π(1)) ≤ C_ℓ^P(π(2)) ≤ ... ≤ C_ℓ^P(π(n)).

  References:
  - Paper §4: Multi-stage chain extension
  - Basic.lean: foldl_max_add_mono, completionAtPosition_mono_release
  - WaterFilling.lean: capacity_bound, ceil_div_le_of_le_mul
-/

import AssemblyFlowShop.Basic
import Mathlib.Tactic
import Mathlib.Order.MinMax
import Mathlib.Data.List.Basic

/-! ## Chain Model

We model an L-stage chain where each stage ℓ has:
- `k ℓ`: number of parallel workers (capacity)
- `w ℓ j`: work for job j at stage ℓ

The completion time of job at position i at stage ℓ depends on:
- Its completion at the previous stage (release time for stage ℓ)
- The processing time at stage ℓ: ⌈W_ℓ(i) / k_ℓ⌉ (water-filling)

For the max-plus recurrence at each stage, the release time of
position i at stage ℓ is the completion time at stage ℓ-1.
-/

/-- Completion time at stage ℓ for the job at position i in
    permutation order, under the max-plus recurrence.

    `release ℓ i` gives the release time of position i at stage ℓ.
    At stage 0, release times come from the external input.
    At stage ℓ > 0, release times are completion times at stage ℓ-1.

    `proc ℓ i` gives the processing time of position i at stage ℓ. -/
def chainCompletion (release : ℕ → ℕ → ℕ) (proc : ℕ → ℕ → ℕ)
    (stage : ℕ) (n : ℕ) : ℕ → ℕ :=
  match stage with
  | 0 => fun i =>
    -- Stage 0: max-plus fold from external release times
    (List.range (i + 1)).foldl
      (fun acc pos => max acc (release 0 pos) + proc 0 pos) 0
  | l + 1 => fun i =>
    -- Stage l+1: release from stage l completion, then fold
    let prevComplete := chainCompletion release proc l n
    (List.range (i + 1)).foldl
      (fun acc pos => max acc (prevComplete pos) + proc (l + 1) pos) 0

/-! ## Priority-Order Completion Lemma

Under preemptive priority with a fixed ordering π, jobs complete each
stage in priority order. That is, the completion times at any stage
are non-decreasing in position:

  C_ℓ^P(π(1)) ≤ C_ℓ^P(π(2)) ≤ ... ≤ C_ℓ^P(π(n))

This follows from the max-plus recurrence structure: each
completion time is at least as large as the previous one, because
  C(i) = max(C(i-1), r(i)) + p(i) ≥ C(i-1) + p(i) ≥ C(i-1)
when p(i) ≥ 0 (which holds for natural numbers).
-/

/-- The max-plus fold accumulator is non-decreasing as we extend
    the range. That is, folding over a longer range gives a larger
    result, because each step adds a non-negative processing time. -/
private theorem foldl_range_step_le (r p : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldl (fun acc pos => max acc (r pos) + p pos) 0 ≤
    (List.range (n + 1)).foldl (fun acc pos => max acc (r pos) + p pos) 0 := by
  simp only [List.range_succ, List.foldl_append, List.foldl_cons,
             List.foldl_nil]
  omega

theorem foldl_completion_mono (r p : ℕ → ℕ) :
    ∀ (i j : ℕ), j ≤ i →
    (List.range (j + 1)).foldl (fun acc pos => max acc (r pos) + p pos) 0 ≤
    (List.range (i + 1)).foldl (fun acc pos => max acc (r pos) + p pos) 0 := by
  intro i
  induction i with
  | zero =>
    intro j hji
    have hj0 : j = 0 := Nat.le_zero.mp hji
    subst hj0; exact le_refl _
  | succ n ih =>
    intro j hji
    by_cases hjn : j ≤ n
    · -- j ≤ n: by IH and transitivity with the step lemma
      exact le_trans (ih j hjn) (foldl_range_step_le r p (n + 1))
    · -- j = n + 1: trivial
      have hje : j = n + 1 := by omega
      subst hje; exact le_refl _

/-- Priority-order completion: under the max-plus fold, completions are
    non-decreasing in position. -/
theorem priority_order_completion (r p : ℕ → ℕ) (i j : ℕ) (h : j ≤ i) :
    (List.range (j + 1)).foldl (fun acc pos => max acc (r pos) + p pos) 0 ≤
    (List.range (i + 1)).foldl (fun acc pos => max acc (r pos) + p pos) 0 :=
  foldl_completion_mono r p i j h

/-! ## Chain-level priority-order completion

If the release times at each stage are non-decreasing (which holds
inductively because completions are non-decreasing), then completions
at every stage are non-decreasing. -/

/-- Chain completions are non-decreasing at every stage.
    This is the multi-stage generalization of priority_order_completion. -/
theorem chainCompletion_mono (release proc : ℕ → ℕ → ℕ) (n : ℕ) :
    ∀ (stage : ℕ) (i j : ℕ), j ≤ i →
    chainCompletion release proc stage n j ≤
    chainCompletion release proc stage n i := by
  intro stage
  induction stage with
  | zero =>
    intro i j hji
    simp only [chainCompletion]
    exact foldl_completion_mono (release 0) (proc 0) i j hji
  | succ l _ih =>
    intro i j hji
    simp only [chainCompletion]
    exact foldl_completion_mono
      (fun pos => chainCompletion release proc l n pos)
      (proc (l + 1)) i j hji

/-! ## Monotonicity: Earlier Arrivals Give Earlier Completions

If the release times at stage ℓ are pointwise ≤ (position by position),
then the completion times at stage ℓ are also pointwise ≤.

This generalizes `foldl_max_add_mono` from Basic.lean to per-position
completion times (not just makespan). -/

/-- Helper: the generalized fold with accumulator is monotone in
    both release times and accumulator. -/
private theorem foldl_range_mono_aux (r₁ r₂ p : ℕ → ℕ) :
    ∀ (n : ℕ), (∀ pos, pos < n → r₁ pos ≤ r₂ pos) →
    ∀ (acc₁ acc₂ : ℕ), acc₁ ≤ acc₂ →
    (List.range n).foldl (fun acc pos => max acc (r₁ pos) + p pos) acc₁ ≤
    (List.range n).foldl (fun acc pos => max acc (r₂ pos) + p pos) acc₂ := by
  intro n
  induction n with
  | zero =>
    intro _ acc₁ acc₂ hacc
    simp only [List.range_zero, List.foldl_nil]
    exact hacc
  | succ k ih =>
    intro hr acc₁ acc₂ hacc
    simp only [List.range_succ, List.foldl_append, List.foldl_cons,
               List.foldl_nil]
    have h_prefix : ∀ pos, pos < k → r₁ pos ≤ r₂ pos := by
      intro pos hp; exact hr pos (by omega)
    have h_mid := ih h_prefix acc₁ acc₂ hacc
    have h_last := hr k (by omega)
    omega

theorem foldl_completion_mono_release (r₁ r₂ p : ℕ → ℕ) (i : ℕ)
    (hr : ∀ pos, pos ≤ i → r₁ pos ≤ r₂ pos) :
    (List.range (i + 1)).foldl (fun acc pos => max acc (r₁ pos) + p pos) 0 ≤
    (List.range (i + 1)).foldl (fun acc pos => max acc (r₂ pos) + p pos) 0 := by
  apply foldl_range_mono_aux
  · intro pos hp; exact hr pos (by omega)
  · exact le_refl 0

/-! ## The Chain Dominance Theorem

**Theorem:** For any L-stage chain and any schedule S, there exists a
preemptive priority schedule P with a single permutation π such that
C_L^P(π(i)) ≤ C_L^S(π(i)) for every job.

We model this as: given arbitrary completion functions (representing
schedule S), there exist release/proc functions for a priority schedule
such that completions are pointwise dominated.

The key structure:
- `S_compl ℓ i`: completion of job i at stage ℓ under schedule S
- The priority schedule P sorts by S_compl at stage L-1, then
  applies the max-plus recurrence at each stage.

For the inductive argument, we need:
1. At stage ℓ, the priority schedule's release times ≤ S's release times
   (in the sorted order).
2. By monotonicity, earlier arrivals give earlier completions.
-/

/-- The abstract chain dominance property for a single stage:
    if release times under the priority schedule are ≤ those
    under any schedule (in priority order), and processing times
    are the same, then completions are ≤.

    This is a direct consequence of per-position monotonicity. -/
theorem single_stage_dominance (r_P r_S p : ℕ → ℕ) (n : ℕ)
    (hr : ∀ i, i < n → r_P i ≤ r_S i) :
    ∀ i, i < n →
    (List.range (i + 1)).foldl (fun acc pos => max acc (r_P pos) + p pos) 0 ≤
    (List.range (i + 1)).foldl (fun acc pos => max acc (r_S pos) + p pos) 0 := by
  intro i hi
  apply foldl_completion_mono_release
  intro pos hpos
  exact hr pos (by omega)

/-- The inductive chain dominance theorem.

    **Statement:** For an L-stage chain, if at each stage the priority
    schedule's release times are dominated by the arbitrary schedule's
    release times (in priority order), then completion times at every
    stage are dominated.

    This captures the inductive structure:
    - Base: release times at stage 0 are dominated (by hypothesis, e.g.,
      from the capacity bound / water-filling construction).
    - Step: if completions at stage ℓ are dominated (inductive hypothesis),
      then they serve as release times at stage ℓ+1, preserving domination.

    Note: The full theorem additionally requires showing that the
    capacity bound produces dominated release times at stage 0. That
    step uses the water-filling construction from WaterFilling.lean.
    Here we formalize the inductive propagation through the chain. -/
theorem chain_dominance_inductive
    (release_P release_S proc : ℕ → ℕ → ℕ) (n : ℕ) (L : ℕ)
    -- Hypothesis: at stage 0, priority release times ≤ schedule release times
    (h_base : ∀ i, i < n → release_P 0 i ≤ release_S 0 i)
    -- Hypothesis: at each subsequent stage, release times come from
    -- the previous stage's completion times (chain coupling)
    -- For the priority schedule:
    (h_chain_P : ∀ (ℓ : ℕ) (i : ℕ), ℓ < L →
      release_P (ℓ + 1) i = chainCompletion release_P proc ℓ n i)
    -- For the arbitrary schedule:
    (h_chain_S : ∀ (ℓ : ℕ) (i : ℕ), ℓ < L →
      release_S (ℓ + 1) i = chainCompletion release_S proc ℓ n i) :
    -- Conclusion: at every stage, priority completions ≤ schedule completions
    ∀ (stage : ℕ), stage ≤ L → ∀ (i : ℕ), i < n →
    chainCompletion release_P proc stage n i ≤
    chainCompletion release_S proc stage n i := by
  intro stage
  induction stage with
  | zero =>
    intro _ i hi
    simp only [chainCompletion]
    apply foldl_completion_mono_release
    intro pos hpos
    exact h_base pos (by omega)
  | succ ℓ ih =>
    intro hℓL i hi
    simp only [chainCompletion]
    -- The release times at stage ℓ+1 are chainCompletion at stage ℓ.
    -- By IH, chainCompletion_P at stage ℓ ≤ chainCompletion_S at stage ℓ.
    apply foldl_completion_mono_release
    intro pos hpos
    exact ih (by omega) pos (by omega)

/-! ## Single-Stage Makespan Invariance

The makespan at any single stage under preemptive priority does not
depend on the priority ordering—only on the arrival times and work.
All k workers are always busy when work is available, so idle time
depends only on the arrival schedule. This yields a short proof of
two-stage chain makespan dominance (Theorem 9 in the paper). -/

/-! ## Chain Dominance: Status

**DISPROVED for L ≥ 3.** Exhaustive search (ConjectureSearch.scala)
found 1,414 makespan counterexamples and 1,016 flowtime
counterexamples over 46,656 configurations (L=3, n=2, k∈{2,3},
work 1–6).

Minimal makespan counterexample: L=3, n=2, k=2, w=[(1,2),(4,1),(1,2)].
  - Sync best makespan: 4.0 (both orderings)
  - Unsync [0,1]|[1,0]: makespan 3.5
  - Gap: 0.5

The mechanism: preemption at stage 1 lets the lighter-at-stage-1 job
pass through quickly, pairing heavier stage-2 work with an earlier
arrival, reducing idle time downstream.

**TRUE for L ≤ 2 (makespan).** By single-stage makespan invariance,
the ordering at the last stage does not affect makespan. For L=2,
any unsynchronized (π₁,π₂) achieves the same makespan as (π₁,π₁),
so the minimum over synchronized schedules equals the global minimum.

The conditional inductive result `chain_dominance_inductive` (proved
above) remains correct: IF base-case release-time domination holds
at stage 0, THEN it propagates through all stages. The failure is
that no single permutation necessarily produces dominated release
times at stage 0 that remain compatible with domination at all
subsequent stages when work inverts across stages. -/

/-- **Chain Dominance** — DISPROVED for L ≥ 3.

    This statement is FALSE in general. Retained as sorry for the
    conditional/L=2 case only. See ConjectureSearch.scala and
    Proposition 10 in the paper for counterexamples. -/
theorem chain_dominance (L n : ℕ) (hL : 0 < L) (hn : 0 < n)
    (S_compl : ℕ → ℕ → ℕ)
    (proc : ℕ → ℕ → ℕ)
    (h_S_chain : ∀ (ℓ : ℕ) (i : ℕ), ℓ < L → i < n →
      S_compl (ℓ + 1) i =
      (List.range (i + 1)).foldl
        (fun acc pos => max acc (S_compl ℓ pos) + proc (ℓ + 1) pos) 0) :
    ∃ (release_P : ℕ → ℕ → ℕ),
      (∀ i, i < n → release_P 0 i ≤ S_compl 0 i) ∧
      (∀ (stage : ℕ), stage ≤ L → ∀ (i : ℕ), i < n →
        chainCompletion release_P proc stage n i ≤
        chainCompletion (fun ℓ => S_compl ℓ) proc stage n i) := by
  sorry -- FALSE for L ≥ 3; see paper Proposition 10
