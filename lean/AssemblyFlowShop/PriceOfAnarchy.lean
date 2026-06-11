/-
  Price of Anarchy: the Universal Makespan UPPER Bound
  =====================================================

  Theorem PoA-1 (upper half) of the price-of-local-ordering note
  (paper/poa/notes.md): no schedule — however badly misordered — can
  exceed

      Cmax ≤ (max availability) + (total stage-2 processing),

  and with balanced splits every availability is bounded by the worst
  per-worker stage-1 load. In the fluid reading this is
  Cmax ≤ 2·W/k, the ceiling that caps the damage of full anarchy at a
  factor of two (against the exact optimum (W + w_max)/k, machine-
  checked in MakespanLowerBound.lean).

  Contents:
  * `depMakespan_le_of_release_bounded` — the max-plus fold bound: a
    dependent stage that processes its (arbitrary) order back-to-back,
    waiting only for releases, finishes by R + Σq whenever all
    releases are ≤ R. Generic in the job index type; definitionally
    equal to `dependentMakespan` of Basic.lean at ℕ.
  * `completionTime_le_load` / `availability_le_load` — on the
    concrete machine model (CapacityBound.lean), every job's
    completion, hence its assembly availability, is at most the worst
    per-worker load. With balanced splits that load is ⌈W/k⌉.
  * `anarchy_makespan_upper` — the composed end-to-end bound.
  * Tightness witnesses, computed: the anti-aligned two-machine
    instance with a withholding downstream reaches exactly 2W, while
    the synchronized schedule on the same work achieves W + w_max.

  Together with MakespanLowerBound.lean this brackets every schedule:
      W + w_max ≤ k·Cmax,   and   Cmax ≤ B + Σq
  — the two halves of the price-of-anarchy analysis.
-/

import AssemblyFlowShop.Basic
import AssemblyFlowShop.CapacityBound
import Mathlib.Tactic

namespace PriceOfAnarchy

open CapacityBound

variable {n k : ℕ} {α : Type*}

/-- Dependent-stage makespan over an arbitrary job index type:
    process the jobs of `τ` back-to-back in order, waiting only for
    each job's release `r j`, with processing times `q j`. At `α = ℕ`
    this is definitionally `dependentMakespan` (Basic.lean). -/
def depMakespan (r q : α → ℕ) (τ : List α) : ℕ :=
  τ.foldl (fun acc j => max acc (r j) + q j) 0

/-- At ℕ, `depMakespan` is the `dependentMakespan` of Basic.lean. -/
theorem depMakespan_eq_dependentMakespan (r q : ℕ → ℕ) (τ : List ℕ) :
    depMakespan r q τ = dependentMakespan r q τ := rfl

/-- The fold bound, with a general accumulator. -/
theorem foldl_maxPlus_le (r q : α → ℕ) (R : ℕ) :
    ∀ (τ : List α), (∀ j ∈ τ, r j ≤ R) → ∀ acc : ℕ,
      τ.foldl (fun acc j => max acc (r j) + q j) acc
        ≤ max acc R + (τ.map q).sum
  | [], _, acc => by simp [le_max_left acc R]
  | j :: τ', h, acc => by
    have hj : r j ≤ R := h j List.mem_cons_self
    have hτ' : ∀ x ∈ τ', r x ≤ R := fun x hx => h x (List.mem_cons_of_mem j hx)
    have ih := foldl_maxPlus_le r q R τ' hτ' (max acc (r j) + q j)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    refine le_trans ih ?_
    have h1 : max (max acc (r j) + q j) R ≤ max acc R + q j := by
      apply max_le
      · exact Nat.add_le_add_right
          (max_le (le_max_left _ _) (le_trans hj (le_max_right _ _))) _
      · exact le_trans (le_max_right acc R) (Nat.le_add_right _ _)
    calc max (max acc (r j) + q j) R + (τ'.map q).sum
        ≤ (max acc R + q j) + (τ'.map q).sum := Nat.add_le_add_right h1 _
      _ = max acc R + (q j + (τ'.map q).sum) := by ring

/-- **The release-bounded makespan bound (PoA-1 upper half, abstract).**
    If every release in `τ` is at most `R`, the dependent stage
    finishes by `R + Σ q` — no matter how badly its order, or the
    upstream orders that produced the releases, are chosen. -/
theorem depMakespan_le_of_release_bounded (r q : α → ℕ) (τ : List α)
    (R : ℕ) (hR : ∀ j ∈ τ, r j ≤ R) :
    depMakespan r q τ ≤ R + (τ.map q).sum := by
  have h := foldl_maxPlus_le r q R τ hR 0
  simpa [depMakespan, Nat.max_eq_right (Nat.zero_le R)] using h

/-- On the concrete machine model, every job's completion time is at
    most the worst per-worker total load. (With balanced splits that
    load is `⌈W/k⌉`; with arbitrary splits it can be as large as the
    total work — which is exactly how split badness stacks on top of
    ordering badness in the empirical sweep.) -/
theorem completionTime_le_load (σ : Equiv.Perm (Fin n))
    (d : Fin n → Fin k → ℕ) (j : Fin n) (B : ℕ)
    (hB : ∀ ℓ, (∑ t, d t ℓ) ≤ B) :
    completionTime σ d j ≤ B := by
  unfold completionTime
  apply Finset.sup_le
  intro ℓ _
  calc finishTime σ d ℓ (σ.symm j)
      ≤ ∑ t, d (σ t) ℓ :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ t, d t ℓ := Equiv.sum_comp σ (fun t => d t ℓ)
    _ ≤ B := hB ℓ

/-- Assembly availability (the max completion over the `m` stage-1
    machines) is at most the worst per-worker load across machines. -/
theorem availability_le_load {m : ℕ}
    (σ : Fin m → Equiv.Perm (Fin n)) (d : Fin m → Fin n → Fin k → ℕ)
    (j : Fin n) (B : ℕ)
    (h_load : ∀ i ℓ, (∑ t, d i t ℓ) ≤ B) :
    Finset.univ.sup (fun i => completionTime (σ i) (d i) j) ≤ B :=
  Finset.sup_le (fun i _ =>
    completionTime_le_load (σ i) (d i) j B (h_load i))

/-- **PoA-1 upper bound, end to end.** In the concrete model with
    per-worker stage-1 loads bounded by `B`, EVERY dependent-stage
    order `τ` finishes by `B + Σ q`. With balanced splits `B = ⌈W/k⌉`
    and fluid stage-2 work `Σ q = ⌈W/k⌉`-ish, this is the
    `Cmax ≤ 2W/k` ceiling: full anarchy can at most double the
    schedule. -/
theorem anarchy_makespan_upper {m : ℕ}
    (σ : Fin m → Equiv.Perm (Fin n)) (d : Fin m → Fin n → Fin k → ℕ)
    (q : Fin n → ℕ) (τ : List (Fin n)) (B : ℕ)
    (h_load : ∀ i ℓ, (∑ t, d i t ℓ) ≤ B) :
    depMakespan
      (fun j => Finset.univ.sup (fun i => completionTime (σ i) (d i) j))
      q τ ≤ B + (τ.map q).sum :=
  depMakespan_le_of_release_bounded _ q τ B
    (fun j _ => availability_le_load σ d j B h_load)

/-! ## Tightness witnesses (computed)

The smallest anti-aligned instance: two jobs of unit work, two stage-1
machines with opposed orders, one worker everywhere (`k = 1`).
Availabilities are then `(2, 2)` — each job is last on one machine.
A withholding downstream (waits for its preferred job) gives makespan
`2W = 4`; the synchronized schedule on the same work gives
`W + w_max = 3`, the exact optimum (MakespanLowerBound.lean). The
fully general construction is in paper/poa/notes.md; these witnesses
machine-check the numbers of its smallest instance. -/

/-- Anti-aligned releases `(2,2)`, unit stage-2 works, any order:
    makespan `4 = 2W`. -/
theorem anarchy_witness_full : maxPlusFold [(2, 1), (2, 1)] = 4 := rfl

/-- Synchronized on the same work: releases `(1,2)` (pipelined), unit
    stage-2 works: makespan `3 = W + w_max`, the optimum. -/
theorem anarchy_witness_sync : maxPlusFold [(1, 1), (2, 1)] = 3 := rfl

end PriceOfAnarchy
