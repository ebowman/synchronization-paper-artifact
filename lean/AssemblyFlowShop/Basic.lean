/-
  Assembly Flow Shop: Stage-2 Recurrence and Pointwise Domination
  ===============================================================

  Problem: divisible-work two-stage assembly flow shop.

  This file formalizes the stage-2 (assembly) side of the paper's
  main dominance theorem at the level of release times:

  * the max-plus recurrence for the dependent (assembly) stage,
    `dependentMakespan` and its per-position refinement
    `completionAtPosition`;
  * monotonicity of both in the release-time vector
    (`dependentMakespan_mono_release`,
    `completionAtPosition_mono_release`);
  * the global-construction dominance theorems
    (`synchronization_global`, `pointwise_stage2_domination` and
    their existential forms), which compose with the capacity bound
    (CapacityBound.lean) and the explicit water-filling allocation
    (WaterFillAllocation.lean).

  The file also records, with a machine-checked counterexample, why
  the classical pairwise-interchange proof technique does not work
  at this level of abstraction; this motivated the global
  construction used in the paper.

  References:
  - Potts, Sevast'janov, Strusevich, Van Wassenhove, Zwaneveld (1995)
  - Lee & Vairaktarakis (1994)
-/

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Order.MinMax

/-! ## The Max-Plus Recurrence

The dependent stage processes jobs in order τ = [j₀, j₁, ..., j_{n-1}].
The completion time after processing position s is:
  D(s) = max(D(s-1), r(τ[s])) + q(τ[s])
with D(-1) = 0.

The makespan is D(n-1).
We model this as a left fold over a list of (release_time, processing_time) pairs.
-/

/-- The max-plus fold: given a list of (release, processing) pairs,
    compute the final completion time. -/
def maxPlusFold : List (ℕ × ℕ) → ℕ :=
  List.foldl (fun acc (r, q) => max acc r + q) 0

/-- Alternate definition: dependent makespan from release and processing functions. -/
def dependentMakespan (r q : ℕ → ℕ) (τ : List ℕ) : ℕ :=
  τ.foldl (fun acc j => max acc (r j) + q j) 0

/-- dependentMakespan equals maxPlusFold applied to the zipped pairs. -/
theorem dependentMakespan_eq_maxPlusFold (r q : ℕ → ℕ) (τ : List ℕ) :
    dependentMakespan r q τ = maxPlusFold (τ.map (fun j => (r j, q j))) := by
  unfold dependentMakespan maxPlusFold
  suffices h : ∀ acc, τ.foldl (fun a j => max a (r j) + q j) acc =
    (τ.map (fun j => (r j, q j))).foldl (fun a (r, q) => max a r + q) acc by
    exact h 0
  intro acc
  induction τ generalizing acc with
  | nil => simp [List.foldl]
  | cons j rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact ih _

/-! ## Monotonicity of the Max-Plus Fold -/

/-- Monotonicity of the fold with respect to the accumulator and release time. -/
private theorem foldl_max_add_mono (r₁ r₂ q : ℕ → ℕ) :
    ∀ (τ : List ℕ), (∀ j ∈ τ, r₁ j ≤ r₂ j) →
    ∀ acc₁ acc₂, acc₁ ≤ acc₂ →
    τ.foldl (fun a j => max a (r₁ j) + q j) acc₁ ≤
    τ.foldl (fun a j => max a (r₂ j) + q j) acc₂ := by
  intro τ
  induction τ with
  | nil => intro _ a₁ a₂ ha; simpa [List.foldl]
  | cons hd tl ih =>
    intro hmem a₁ a₂ ha
    simp only [List.foldl_cons]
    have hr : r₁ hd ≤ r₂ hd := by
      apply hmem; simp
    have h_rest : ∀ k ∈ tl, r₁ k ≤ r₂ k := by
      intro k hk; apply hmem; simp [hk]
    have h_step : max a₁ (r₁ hd) + q hd ≤ max a₂ (r₂ hd) + q hd := by
      apply Nat.add_le_add_right; exact sup_le_sup ha hr
    exact ih h_rest _ _ h_step

/-- Monotonicity: if r₁ ≤ r₂ pointwise on τ, then dependentMakespan r₁ ≤ dependentMakespan r₂. -/
theorem dependentMakespan_mono_release (r₁ r₂ q : ℕ → ℕ) (τ : List ℕ)
    (h : ∀ j ∈ τ, r₁ j ≤ r₂ j) :
    dependentMakespan r₁ q τ ≤ dependentMakespan r₂ q τ := by
  exact foldl_max_add_mono r₁ r₂ q τ h 0 0 (Nat.le_refl 0)

/-! ## Why Not Pairwise Interchange?

The classical proof of permutation-schedule dominance (Potts et al.
1995) transforms a schedule by adjacent pairwise exchanges. At the
release-time abstraction used in this development, that route fails:
the bounds available after a single stage-1 swap —

  r' j  ≤ min (r j) (r j'),
  r' j' ≥ max (r j) (r j'),
  r' h  = r h  for all other jobs h —

do *not* imply that some reordering of the assembly stage achieves a
makespan no larger than the original. The machine-checked
counterexample below witnesses this with two jobs: the original
releases r = (5, 1) processed in order [1, 0] achieve makespan 12,
while after the swap (r' = (1, 5)) *both* possible orders are
strictly worse (15 and 16).

The failure is informative: a pairwise swap fixes the work divisions
of the intermediate schedules, but the optimal permutation schedule
re-optimizes all divisions at once. This is why the paper's theorem
is proved by the global construction in the next section, which
rebuilds every release time in a single step instead of tracking
exchanges. -/

namespace InterchangeCounterexample

/-- Original release times: job 0 releases at 5, job 1 at 1. -/
def r : ℕ → ℕ := fun j => if j = 0 then 5 else 1

/-- Release times after the abstract swap: job 0 at 1, job 1 at 5.
    These satisfy the swap bounds: r' 0 = 1 ≤ min (r 0) (r 1) and
    r' 1 = 5 ≥ max (r 0) (r 1). -/
def r' : ℕ → ℕ := fun j => if j = 0 then 1 else 5

/-- Stage-2 processing times: job 0 takes 1, job 1 takes 10. -/
def q : ℕ → ℕ := fun j => if j = 0 then 1 else 10

/-- The original schedule (order [1, 0]) achieves makespan 12. -/
example : dependentMakespan r q [1, 0] = 12 := by decide

/-- After the swap, order [0, 1] gives makespan 15 > 12. -/
example : dependentMakespan r' q [0, 1] = 15 := by decide

/-- After the swap, order [1, 0] gives makespan 16 > 12. -/
example : dependentMakespan r' q [1, 0] = 16 := by decide

/-- Both post-swap orders — i.e. every permutation of the two jobs —
    exceed the original makespan: the interchange step cannot be
    repaired by re-sequencing the assembly stage. -/
example :
    dependentMakespan r q [1, 0] <
      min (dependentMakespan r' q [0, 1]) (dependentMakespan r' q [1, 0]) := by
  decide

end InterchangeCounterexample

/-! ## The Global Construction

**Key insight:** in the full model, all stage-1 machines process the
same jobs. Copying one machine's permutation and work divisions to
all machines makes the machines identical, so the release time of
every job equals that machine's completion time — which is ≤ the
original release time (the original release was a max over all
machines). Composing with stage-2 monotonicity gives dominance.

In the heterogeneous-work model the copy step is replaced by the
capacity bound and water-filling (CapacityBound.lean,
WaterFillAllocation.lean, WaterFilling.lean), which produce
release times r* ≤ r pointwise by a different route; the
monotonicity composition below is shared by both arguments.
-/

/-- Copying any single machine's schedule gives release times
    pointwise ≤ the original release times (which are the max over
    machines). -/
theorem copy_team_release_le
    {m : ℕ} (C : Fin m → ℕ → ℕ)
    (r : ℕ → ℕ)
    (hr : ∀ j, ∀ i : Fin m, C i j ≤ r j)
    (team : Fin m) :
    ∀ j, C team j ≤ r j :=
  fun j => hr j team

/-- The synchronization theorem via global construction.

    For any schedule with release times r (arising from m stage-1
    machines), the synchronized schedule that copies one machine has
    release times ≤ r pointwise, hence achieves makespan ≤ the
    original with the same stage-2 order. -/
theorem synchronization_global
    {m : ℕ}
    (C : Fin m → ℕ → ℕ)   -- completion times per machine
    (r : ℕ → ℕ)            -- release = max over machines
    (hr : ∀ j, ∀ i : Fin m, C i j ≤ r j)  -- each machine ≤ release
    (q : ℕ → ℕ)            -- dependent processing times
    (τ : List ℕ)            -- dependent order
    (team : Fin m)          -- which machine to copy
    : dependentMakespan (C team) q τ ≤ dependentMakespan r q τ := by
  apply dependentMakespan_mono_release
  intro j _
  exact hr j team

/-- Existential form: among all schedules, there exists a synchronized
    one with makespan ≤ any given schedule. -/
theorem synchronization_exists
    {m : ℕ}
    (C : Fin m → ℕ → ℕ)
    (r : ℕ → ℕ)
    (hr : ∀ j, ∀ i : Fin m, C i j ≤ r j)
    (q : ℕ → ℕ) (τ : List ℕ) (team : Fin m) :
    ∃ r_sync : ℕ → ℕ,
      (∀ j, r_sync j ≤ r j) ∧
      dependentMakespan r_sync q τ ≤ dependentMakespan r q τ :=
  ⟨C team, fun j => hr j team, synchronization_global C r hr q τ team⟩

/-! ## Pointwise Per-Position Stage-2 Domination

The paper's main theorem claims pointwise domination:
  C^(2)_j(S*) ≤ C^(2)_j(S) for every job j.

This is stronger than makespan domination. The argument:
1. r*_j ≤ r_j for all j (from the construction).
2. The stage-2 fold value at every position s is monotone in the
   release times.
3. Job j's completion time is the fold value at position τ⁻¹(j).
4. Therefore C^(2)_j(S*) ≤ C^(2)_j(S) for every j.

We formalize step 2 by folding over prefixes of τ.
For multiple stage-2 workers, each worker has its own fold with its
own processing times, and the job completion time is the max over
workers. Since each fold is independently monotone, the max is also
monotone. We formalize the single-worker case; the multi-worker
extension is a direct corollary. -/

/-- Stage-2 worker completion time after processing the first (s+1) jobs
    in order τ. This is the max-plus fold over the prefix τ.take (s+1). -/
def completionAtPosition (r q : ℕ → ℕ) (τ : List ℕ) (s : ℕ) : ℕ :=
  (τ.take (s + 1)).foldl (fun acc j => max acc (r j) + q j) 0

/-- The full makespan equals the completion at the last position. -/
theorem dependentMakespan_eq_completionAtPosition (r q : ℕ → ℕ) (τ : List ℕ)
    (hne : τ ≠ []) :
    dependentMakespan r q τ = completionAtPosition r q τ (τ.length - 1) := by
  unfold dependentMakespan completionAtPosition
  congr 1
  have hpos : 0 < τ.length := by
    cases τ with | nil => exact absurd rfl hne | cons _ _ => simp
  have h : τ.length - 1 + 1 = τ.length := Nat.succ_pred_eq_of_pos hpos
  rw [h, List.take_length]

/-- Pointwise per-position monotonicity: if r₁ ≤ r₂ pointwise on τ,
    then the completion time at every position s is no larger.

    This is the key strengthening from makespan domination to
    pointwise per-job domination in the paper's main theorem. -/
theorem completionAtPosition_mono_release (r₁ r₂ q : ℕ → ℕ) (τ : List ℕ) (s : ℕ)
    (h : ∀ j ∈ τ, r₁ j ≤ r₂ j) :
    completionAtPosition r₁ q τ s ≤ completionAtPosition r₂ q τ s := by
  unfold completionAtPosition
  apply foldl_max_add_mono r₁ r₂ q (τ.take (s + 1))
  · intro j hj
    exact h j (List.take_subset (s + 1) τ hj)
  · exact Nat.le_refl 0

/-- Pointwise stage-2 domination (the paper's main theorem at the
    release-time level): the synchronized schedule with release times
    C(team) ≤ r pointwise achieves completion time ≤ original at
    EVERY position in the stage-2 order. Since job j's completion
    time is the fold value at position τ⁻¹(j), this gives
    C^(2)_j(S*) ≤ C^(2)_j(S) for every j. -/
theorem pointwise_stage2_domination
    {m : ℕ}
    (C : Fin m → ℕ → ℕ)
    (r : ℕ → ℕ)
    (hr : ∀ j, ∀ i : Fin m, C i j ≤ r j)
    (q : ℕ → ℕ)
    (τ : List ℕ)
    (team : Fin m)
    (s : ℕ) :
    completionAtPosition (C team) q τ s ≤ completionAtPosition r q τ s := by
  apply completionAtPosition_mono_release
  intro j _
  exact hr j team

/-- Existential form of pointwise domination: there exists a synchronized
    release-time function that dominates the original at every position. -/
theorem pointwise_domination_exists
    {m : ℕ}
    (C : Fin m → ℕ → ℕ)
    (r : ℕ → ℕ)
    (hr : ∀ j, ∀ i : Fin m, C i j ≤ r j)
    (q : ℕ → ℕ) (τ : List ℕ) (team : Fin m) :
    ∃ r_sync : ℕ → ℕ,
      (∀ j, r_sync j ≤ r j) ∧
      (∀ s, completionAtPosition r_sync q τ s ≤ completionAtPosition r q τ s) :=
  ⟨C team,
   fun j => hr j team,
   fun s => pointwise_stage2_domination C r hr q τ team s⟩

/-! ## Proof Status

Every declaration in this file is proved; the file contains no
`sorry`. The dominance results depend only on `foldl_max_add_mono`
(proved above) and `sup_le_sup` from Mathlib.

- `dependentMakespan_mono_release`, `completionAtPosition_mono_release`:
  stage-2 monotonicity in the release-time vector.
- `synchronization_global` / `synchronization_exists`: makespan
  dominance via the global construction.
- `pointwise_stage2_domination` / `pointwise_domination_exists`:
  per-position (hence per-job) dominance.
- `InterchangeCounterexample`: machine-checked witness that the
  pairwise-interchange route fails at this abstraction.
-/
