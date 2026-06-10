/-
  Water-Filling Composition for Heterogeneous Work
  ==================================================

  This file composes the paper's main dominance theorem
  (permutation-schedule dominance for the divisible-work two-stage
  assembly flow shop with heterogeneous w_{i,j}) at the
  release-time level:

  1. Capacity bound: W_i(s) ≤ k * r_{π(s)} when π sorts jobs by
     non-decreasing release time. Derived from the concrete machine
     model in CapacityBound.lean (`capacity_bound_concrete`); taken
     as a hypothesis here.
  2. Ceiling bound (`ceil_div_le_of_le_mul`):
     ⌈W_i(s)/k⌉ ≤ r_{π(s)}, since r is a natural number.
  3. Composition with stage-2 monotonicity (Basic.lean):
     release times r* ≤ r pointwise give makespan(S*) ≤ makespan(S).

  The explicit allocation achieving completion ⌈W_i(s)/k⌉ at every
  position is constructed in WaterFillAllocation.lean.
-/

import AssemblyFlowShop.Basic
import Mathlib.Tactic
import Mathlib.Order.MinMax

/-! ## The Ceiling Bound -/

/-- The ceiling bound: if W ≤ k * r and r is a natural number,
    then ⌈W/k⌉ ≤ r.

    This is the step from the capacity bound to release-time
    domination; it is where integrality of the release times is
    used. -/
theorem ceil_div_le_of_le_mul (W k r : ℕ) (hk : 0 < k)
    (h : W ≤ k * r) :
    (W + k - 1) / k ≤ r := by
  -- By Nat.div_le_iff: a / b ≤ c ↔ a ≤ b * c + (b - 1)  (for b > 0),
  -- and W + k - 1 ≤ k * r + k - 1 follows from W ≤ k * r.
  rw [Nat.div_le_iff_le_mul_add_pred hk]
  omega

/-! ## Release-Time Domination

Given:
- m machines, each with k workers;
- for each machine i, cumulative work W_i(s) on jobs π(1)..π(s);
- release times r(j) = max_i C_i(j) from the original schedule;
- π sorts jobs by non-decreasing r.

The water-filling construction gives each machine completion times
⌈W_i(s)/k⌉ at position s (WaterFillAllocation.lean). By the
capacity bound, ⌈W_i(s)/k⌉ ≤ r(π(s)). Taking the max over machines:
r*(π(s)) = max_i ⌈W_i(s)/k⌉ ≤ r(π(s)).

So r* ≤ r pointwise, and by stage-2 monotonicity (Basic.lean),
makespan(S*) ≤ makespan(S). -/

/-- Water-filling release times are dominated by original release
    times: for each machine i and position s, ⌈W_i(s)/k⌉ ≤ r(s).

    The capacity hypothesis is discharged from the concrete machine
    model by `CapacityBound.capacity_bound_concrete`. -/
theorem waterfill_release_le
    {m : ℕ} (k : ℕ) (hk : 0 < k)
    -- W_i(s) = cumulative work on machine i for the first s jobs in order π
    (W : Fin m → ℕ → ℕ)
    -- r(s) = original release time of the s-th job in order π
    (r : ℕ → ℕ)
    -- Capacity bound: W_i(s) ≤ k * r(s) for all machines i and positions s
    (h_capacity : ∀ (i : Fin m) (s : ℕ), W i s ≤ k * r s)
    : ∀ (i : Fin m) (s : ℕ), (W i s + k - 1) / k ≤ r s :=
  fun i s => ceil_div_le_of_le_mul (W i s) k (r s) hk (h_capacity i s)

/-- Composition with stage-2 monotonicity: synchronized release
    times r_wf ≤ r pointwise give a makespan no larger than the
    original, for any stage-2 order. -/
theorem waterfill_synchronization
    (r r_wf : ℕ → ℕ)
    (h_rwf : ∀ j, r_wf j ≤ r j)
    (q : ℕ → ℕ) (τ : List ℕ)
    : dependentMakespan r_wf q τ ≤ dependentMakespan r q τ := by
  apply dependentMakespan_mono_release
  intro j _
  exact h_rwf j

/-- The full existential form: given the capacity bound for each
    machine, the synchronized release times
    r*(s) = max_i ⌈W_i(s)/k⌉ satisfy r* ≤ r pointwise and give a
    makespan no larger than the original. -/
theorem waterfill_exists
    {m : ℕ} [NeZero m] (k : ℕ) (hk : 0 < k)
    (W : Fin m → ℕ → ℕ)
    (r : ℕ → ℕ)
    (h_capacity : ∀ (i : Fin m) (s : ℕ), W i s ≤ k * r s)
    (q : ℕ → ℕ) (τ : List ℕ) :
    ∃ r_wf : ℕ → ℕ,
      (∀ j, r_wf j ≤ r j) ∧
      dependentMakespan r_wf q τ ≤ dependentMakespan r q τ := by
  -- Witness: for each job s, take the max over machines of ⌈W_i(s)/k⌉
  refine ⟨fun s => Finset.sup' Finset.univ ⟨⟨0, Fin.pos'⟩, Finset.mem_univ _⟩
    (fun i => (W i s + k - 1) / k), ?_, ?_⟩
  · intro j
    apply Finset.sup'_le
    intro i _
    exact waterfill_release_le k hk W r h_capacity i j
  · apply dependentMakespan_mono_release
    intro j _
    apply Finset.sup'_le
    intro i _
    exact waterfill_release_le k hk W r h_capacity i j

/-! ## Proof Status

Every declaration in this file is proved; the file contains no
`sorry`.

- `ceil_div_le_of_le_mul`: ⌈W/k⌉ ≤ r when W ≤ k*r.
- `waterfill_release_le`: per-machine release-time domination.
- `waterfill_synchronization`: composition with stage-2 monotonicity.
- `waterfill_exists`: the existential form across m machines.

The capacity hypothesis `h_capacity` is derived from the concrete
machine model (orders, work divisions, per-worker finish times) in
CapacityBound.lean; the explicit allocation achieving ⌈W_i(s)/k⌉
at every position is constructed in WaterFillAllocation.lean.
-/
