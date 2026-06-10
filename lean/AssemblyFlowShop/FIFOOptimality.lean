/-
  FIFO Optimality and Permutation-Schedule Dominance
  ===================================================

  Two results about the dependent (assembly) stage:

  **FIFO optimality for C_max:**
  On a single non-preemptive machine with release times r and
  processing times q, sorting jobs by non-decreasing release time
  (FIFO) minimises C_max.

  Proof: adjacent interchange. If τ is non-FIFO, a maximal-release
  job can be bubbled to the last position by adjacent swaps, none of
  which increases C_max (`adjacent_swap_fifo`); induction on the
  sorted list does the rest (`fifo_optimality`).

  **Permutation-schedule dominance for C_max:**
  Composing release-time domination (WaterFilling.lean) with FIFO
  optimality gives: there exists a permutation schedule, with the
  stage-1 permutation also used at stage 2, that minimises C_max
  (`permutation_schedule_dominance`).

  References:
  - Basic.lean: dependentMakespan, dependentMakespan_mono_release
  - WaterFilling.lean: waterfill_exists
-/

import AssemblyFlowShop.Basic
import AssemblyFlowShop.WaterFilling
import Mathlib.Tactic
import Mathlib.Order.MinMax
import Mathlib.Data.List.Basic

set_option linter.style.longLine false

/-! ## Adjacent Swap Lemma

The core of the FIFO proof: swapping two adjacent jobs where the
first has a (weakly) larger release time does not increase C_max. -/

/-- The fold step function is monotone in its accumulator. -/
private theorem fold_step_mono (r q : ℕ → ℕ) (j : ℕ)
    (a₁ a₂ : ℕ) (h : a₁ ≤ a₂) :
    max a₁ (r j) + q j ≤ max a₂ (r j) + q j := by
  omega

/-- The fold over a suffix is monotone in the initial accumulator. -/
private theorem foldl_suffix_mono (r q : ℕ → ℕ) (l : List ℕ) :
    ∀ (a₁ a₂ : ℕ), a₁ ≤ a₂ →
    l.foldl (fun a j => max a (r j) + q j) a₁ ≤
    l.foldl (fun a j => max a (r j) + q j) a₂ := by
  induction l with
  | nil => intro a₁ a₂ h; simpa [List.foldl]
  | cons hd tl ih =>
    intro a₁ a₂ h
    simp only [List.foldl_cons]
    exact ih _ _ (fold_step_mono r q hd a₁ a₂ h)

/-- **Adjacent-swap lemma for FIFO optimality.**

    Consider the fold over pre ++ [a, b] ++ suf.
    If r(a) ≥ r(b), swapping to get pre ++ [b, a] ++ suf
    does not increase the fold result. -/
theorem adjacent_swap_fifo (r q : ℕ → ℕ) (pre suf : List ℕ)
    (a b : ℕ)
    (h_release : r b ≤ r a) :
    dependentMakespan r q (pre ++ [b, a] ++ suf) ≤
    dependentMakespan r q (pre ++ [a, b] ++ suf) := by
  unfold dependentMakespan
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply foldl_suffix_mono
  -- Goal: max (max B (r b) + q b) (r a) + q a
  --     ≤ max (max B (r a) + q a) (r b) + q b
  -- where B is the fold over pre. Since r b ≤ r a, both sides
  -- reduce to max B (r a) + q a + q b.
  omega

/-! ## Bubbling a Maximal-Release Job to the End -/

/-- Appending a final job: the makespan of `l ++ [M]` is one fold
    step applied to the makespan of `l`. -/
private theorem dependentMakespan_append_singleton (r q : ℕ → ℕ)
    (l : List ℕ) (M : ℕ) :
    dependentMakespan r q (l ++ [M]) =
    max (dependentMakespan r q l) (r M) + q M := by
  unfold dependentMakespan
  simp [List.foldl_append]

/-- A job whose release time dominates everything after it can be
    bubbled to the last position without increasing the makespan:
    each adjacent swap is justified by `adjacent_swap_fifo`. -/
private theorem bubble_max_to_end (r q : ℕ → ℕ) (M : ℕ) :
    ∀ (suf pre : List ℕ), (∀ c ∈ suf, r c ≤ r M) →
    dependentMakespan r q (pre ++ suf ++ [M]) ≤
    dependentMakespan r q (pre ++ M :: suf) := by
  intro suf
  induction suf with
  | nil =>
    intro pre _
    simp
  | cons c rest ih =>
    intro pre hsuf
    have hc : r c ≤ r M := hsuf c (by simp)
    have hrest : ∀ x ∈ rest, r x ≤ r M := fun x hx => hsuf x (by simp [hx])
    calc dependentMakespan r q (pre ++ (c :: rest) ++ [M])
        = dependentMakespan r q ((pre ++ [c]) ++ rest ++ [M]) := by
          simp
      _ ≤ dependentMakespan r q ((pre ++ [c]) ++ M :: rest) := ih (pre ++ [c]) hrest
      _ = dependentMakespan r q (pre ++ [c, M] ++ rest) := by
          simp
      _ ≤ dependentMakespan r q (pre ++ [M, c] ++ rest) :=
          adjacent_swap_fifo r q pre rest M c hc
      _ = dependentMakespan r q (pre ++ M :: c :: rest) := by
          simp

/-! ## FIFO Optimality -/

private theorem fifo_optimality_aux (r q : ℕ → ℕ) :
    ∀ (τ_sorted : List ℕ),
    τ_sorted.Pairwise (fun a b => r a ≤ r b) →
    ∀ (τ : List ℕ), τ_sorted.Perm τ →
    dependentMakespan r q τ_sorted ≤ dependentMakespan r q τ := by
  intro τ_sorted
  induction τ_sorted using List.reverseRecOn with
  | nil =>
    intro _ τ hperm
    rw [hperm.symm.eq_nil]
  | append_singleton init M ih =>
    intro h_sorted τ hperm
    -- Unpack sortedness: init is sorted and everything in init is ≤ M.
    rw [List.pairwise_append] at h_sorted
    obtain ⟨h_init, _, h_le⟩ := h_sorted
    have h_max_init : ∀ a ∈ init, r a ≤ r M :=
      fun a ha => h_le a ha M (by simp)
    -- M occurs in τ; split τ around it.
    have hM : M ∈ τ := hperm.mem_iff.mp (by simp)
    obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hM
    -- init is a permutation of the rest of τ.
    have hperm' : init.Perm (pre ++ suf) := by
      have h1 : (M :: init).Perm (M :: (pre ++ suf)) :=
        ((List.perm_append_singleton M init).symm.trans hperm).trans
          List.perm_middle
      exact h1.cons_inv
    -- Everything after M in τ has release time ≤ r M.
    have h_suf : ∀ c ∈ suf, r c ≤ r M := by
      intro c hc
      have hcτ : c ∈ init ++ [M] :=
        hperm.mem_iff.mpr (by simp [hc])
      rcases List.mem_append.mp hcτ with hci | hcM
      · exact h_max_init c hci
      · simp at hcM; subst hcM; exact le_refl _
    -- Chain the three estimates.
    calc dependentMakespan r q (init ++ [M])
        = max (dependentMakespan r q init) (r M) + q M :=
          dependentMakespan_append_singleton r q init M
      _ ≤ max (dependentMakespan r q (pre ++ suf)) (r M) + q M := by
          have := ih h_init (pre ++ suf) hperm'
          omega
      _ = dependentMakespan r q ((pre ++ suf) ++ [M]) :=
          (dependentMakespan_append_singleton r q (pre ++ suf) M).symm
      _ = dependentMakespan r q (pre ++ suf ++ [M]) := by
          simp
      _ ≤ dependentMakespan r q (pre ++ M :: suf) :=
          bubble_max_to_end r q M suf pre h_suf

/-- **FIFO Optimality.**

    On a single non-preemptive machine, sorting jobs by
    non-decreasing release time (FIFO) minimises C_max: the sorted
    order achieves a makespan no larger than any permutation of it. -/
theorem fifo_optimality (r q : ℕ → ℕ) (τ τ_sorted : List ℕ)
    (hperm : τ_sorted.Perm τ)
    (h_sorted : τ_sorted.Pairwise (fun a b => r a ≤ r b)) :
    dependentMakespan r q τ_sorted ≤ dependentMakespan r q τ :=
  fifo_optimality_aux r q τ_sorted h_sorted τ hperm

/-! ## Permutation-Schedule Dominance for C_max

Combining:
- release-time domination (waterfill_exists, WaterFilling.lean):
    ∃ r_wf ≤ r pointwise;
- stage-2 monotonicity (dependentMakespan_mono_release, Basic.lean):
    r_wf ≤ r → C(τ) does not increase;
- FIFO optimality (fifo_optimality, above): the sorted order of
    r_wf minimises C_max over stage-2 orders.

Gives: a permutation schedule (same permutation at stage 1 and
stage 2) with C_max ≤ any schedule. -/

/-- **Permutation-schedule dominance for C_max.**

    For any schedule with release times r and stage-2 order τ, the
    permutation schedule that water-fills stage 1 (release times
    r_wf ≤ r, supplied by `waterfill_exists`) and processes stage 2
    in the FIFO order of r_wf has C_max ≤ C_max of the original
    schedule. -/
theorem permutation_schedule_dominance
    (r r_wf q : ℕ → ℕ) (τ π_list : List ℕ)
    (hperm : π_list.Perm τ)
    (h_rwf_le : ∀ j, r_wf j ≤ r j)
    (h_rwf_sorted :
      π_list.Pairwise (fun a b => r_wf a ≤ r_wf b)) :
    dependentMakespan r_wf q π_list ≤
    dependentMakespan r q τ := by
  calc dependentMakespan r_wf q π_list
      ≤ dependentMakespan r_wf q τ :=
        fifo_optimality r_wf q τ π_list hperm h_rwf_sorted
    _ ≤ dependentMakespan r q τ :=
        dependentMakespan_mono_release r_wf r q τ
          (fun j _ => h_rwf_le j)

/-! ## Proof Status

Every declaration in this file is proved; the file contains no
`sorry`.

- `adjacent_swap_fifo`: the adjacent-interchange kernel.
- `bubble_max_to_end`: iterated swaps move a maximal-release job to
  the last position without increasing C_max.
- `fifo_optimality`: FIFO order minimises C_max (induction on the
  sorted list).
- `permutation_schedule_dominance`: composition with release-time
  domination and stage-2 monotonicity.
-/
