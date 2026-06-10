/-
  An Explicit Water-Filling Allocation
  =====================================

  WaterFillFeasibility.lean proves the *arithmetic* skeleton of the
  water-filling lemma (ceiling/floor spread, ceiling growth). This
  file proves the lemma itself, constructively: it exhibits work
  divisions and shows they have the three properties the paper's
  water-filling lemma claims.

  The construction: number the work units of machine i consecutively
  along the job sequence π (units 0, 1, 2, … in ℕ). Worker ℓ takes
  exactly the units u with u % k = ℓ. Then after X cumulative units,
  worker ℓ holds  load X ℓ = #{u < X : u % k = ℓ}  units, and:

  (1) load is monotone in X, so each job's division
      d ℓ = load X' ℓ - load X ℓ is a nonnegative integer;
  (2) Σ_ℓ load X ℓ = X — the divisions sum to each job's work;
  (3) max_ℓ load X ℓ = ⌈X/k⌉ — the completion time at each
      position s is ⌈W_i(s)/k⌉, as the water-filling lemma states.

  This is the allocation the paper's one-unit-at-a-time
  least-loaded procedure produces (with round-robin tie-breaking),
  but it needs no invariant induction and no tie-breaking analysis.
-/

import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Div

namespace WaterFillAllocation

variable {k : ℕ}

/-- The load of worker `ℓ` after `X` cumulative work units:
    the number of units `u < X` in `ℓ`'s residue class mod `k`. -/
def load (k : ℕ) (X : ℕ) (ℓ : Fin k) : ℕ :=
  ((Finset.range X).filter (fun u => u % k = ℓ.val)).card

/-- Loads only grow as cumulative work grows; hence per-job
    divisions `load X' ℓ - load X ℓ` are nonnegative integers. -/
theorem load_monotone (ℓ : Fin k) : Monotone (fun X => load k X ℓ) := by
  intro X X' h
  apply Finset.card_le_card
  intro u hu
  rw [Finset.mem_filter, Finset.mem_range] at hu ⊢
  exact ⟨lt_of_lt_of_le hu.1 h, hu.2⟩

/-- TOTAL WORK: the worker loads partition the `X` work units,
    so they sum to `X`. Hence the divisions of each job sum to
    that job's work requirement. -/
theorem sum_load (hk : 0 < k) (X : ℕ) :
    ∑ ℓ : Fin k, load k X ℓ = X := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun u => (⟨u % k, Nat.mod_lt u hk⟩ : Fin k))
    (s := Finset.range X) (t := Finset.univ)
    (fun u _ => Finset.mem_univ _)
  rw [Finset.card_range] at h
  calc ∑ ℓ : Fin k, load k X ℓ
      = ∑ ℓ : Fin k, ((Finset.range X).filter
          (fun u => (⟨u % k, Nat.mod_lt u hk⟩ : Fin k) = ℓ)).card := by
        apply Finset.sum_congr rfl
        intro ℓ _
        unfold load
        congr 1
        apply Finset.filter_congr
        intro u _
        simp [Fin.ext_iff]
    _ = X := h.symm

/-- Worker 0 is (weakly) the most loaded: subtracting `ℓ` injects
    `ℓ`'s units into worker 0's units. -/
theorem load_le_load_zero (hk : 0 < k) (X : ℕ) (ℓ : Fin k) :
    load k X ℓ ≤ load k X ⟨0, hk⟩ := by
  classical
  apply Finset.card_le_card_of_injOn (fun u => u - ℓ.val)
  · -- maps to: u - ℓ is a unit of worker 0 below X
    intro u hu
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨huX, humod⟩ := hu
    have hle : ℓ.val ≤ u := humod ▸ Nat.mod_le u k
    have hdecomp : k * (u / k) + u % k = u := Nat.div_add_mod u k
    have hsub : u - ℓ.val = k * (u / k) := by omega
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · show u - ℓ.val < X
      omega
    · show (u - ℓ.val) % k = (0 : ℕ)
      rw [hsub]
      exact Nat.mul_mod_right k (u / k)
  · -- injective on ℓ's units (all are ≥ ℓ, so subtraction is faithful)
    intro u hu u' hu' heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hu hu'
    have heq' : u - ℓ.val = u' - ℓ.val := heq
    have h1 : ℓ.val ≤ u := hu.2 ▸ Nat.mod_le u k
    have h2 : ℓ.val ≤ u' := hu'.2 ▸ Nat.mod_le u' k
    omega

/-- Worker 0's load is exactly `⌈X/k⌉`: its units are the multiples
    of `k` below `X`. -/
theorem load_zero_eq (hk : 0 < k) (X : ℕ) :
    load k X ⟨0, hk⟩ = X ⌈/⌉ k := by
  classical
  -- v < X ⌈/⌉ k ↔ k * v < X, from the ceilDiv Galois connection.
  have key : ∀ v : ℕ, k * v < X ↔ v < X ⌈/⌉ k := by
    intro v
    rw [← not_iff_not, not_lt, not_lt]
    exact ⟨fun h => (ceilDiv_le_iff_le_mul hk).mpr h,
           fun h => (ceilDiv_le_iff_le_mul hk).mp h⟩
  unfold load
  rw [← Finset.card_range (X ⌈/⌉ k)]
  symm
  apply Finset.card_bij (fun v _ => k * v)
  · -- multiples of k below X are worker 0's units
    intro v hv
    rw [Finset.mem_range] at hv
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨(key v).mpr hv, Nat.mul_mod_right k v⟩
  · -- injective
    intro v hv v' hv' heq
    exact Nat.eq_of_mul_eq_mul_left hk heq
  · -- surjective: every worker-0 unit is k * (u / k)
    intro u hu
    rw [Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨huX, humod⟩ := hu
    have hcancel : k * (u / k) = u :=
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero humod)
    refine ⟨u / k, ?_, hcancel⟩
    rw [Finset.mem_range]
    exact (key (u / k)).mp (by rw [hcancel]; exact huX)

/-- MAXIMUM LOAD: after `X` cumulative units the most-loaded worker
    holds exactly `⌈X/k⌉` units. This is the completion time the
    paper's water-filling lemma claims at every position. -/
theorem sup_load (hk : 0 < k) (X : ℕ) :
    Finset.univ.sup (fun ℓ : Fin k => load k X ℓ) = X ⌈/⌉ k := by
  apply le_antisymm
  · apply Finset.sup_le
    intro ℓ _
    calc load k X ℓ ≤ load k X ⟨0, hk⟩ := load_le_load_zero hk X ℓ
      _ = X ⌈/⌉ k := load_zero_eq hk X
  · rw [← load_zero_eq hk X]
    exact Finset.le_sup (f := fun ℓ : Fin k => load k X ℓ) (Finset.mem_univ _)

/-- **The water-filling lemma, constructive form.**

    For any cumulative-work profile `W` (where `W s` is the total
    work of the first `s` jobs in the chosen permutation, so
    `W s' - W s` is the work between positions), there is a
    per-worker cumulative schedule `F` such that:

    (1) each worker's cumulative load is non-decreasing in the
        cumulative work — i.e. the induced per-job divisions are
        nonnegative integers;
    (2) at every position the worker loads sum to `W s` — the
        divisions of each job sum to that job's work requirement;
    (3) the most-loaded worker — the machine's completion time at
        position `s` — is exactly `⌈W s / k⌉`. -/
theorem waterfill_allocation_exists (hk : 0 < k) (W : ℕ → ℕ) :
    ∃ F : Fin k → ℕ → ℕ,
      (∀ ℓ s s', W s ≤ W s' → F ℓ s ≤ F ℓ s') ∧
      (∀ s, ∑ ℓ : Fin k, F ℓ s = W s) ∧
      (∀ s, Finset.univ.sup (fun ℓ => F ℓ s) = W s ⌈/⌉ k) := by
  refine ⟨fun ℓ s => load k (W s) ℓ, ?_, ?_, ?_⟩
  · intro ℓ s s' h
    exact load_monotone ℓ h
  · intro s
    exact sum_load hk (W s)
  · intro s
    exact sup_load hk (W s)

end WaterFillAllocation
