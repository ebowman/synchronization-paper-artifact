/-
  The Universal Makespan Lower Bound  k·Cmax ≥ W + w(M)
  ======================================================

  Theorem S1(a) of the stochastic note (paper/stochastic/notes.md):
  in the homogeneous two-stage assembly flow shop (every job j needs
  w j units on each of the m stage-1 machines and w j units on the
  assembly stage; every machine has k unit-rate workers), EVERY
  schedule satisfies

      k · Cmax  ≥  (Σ_j w j) + w M      for every job M,

  in particular with M a maximum-work job. Since the synchronized
  schedule achieves the matching value, this pins the synchronized
  makespan as the exact optimum, independent of the shared order —
  the formal content behind "the list needs to be SHARED, not RIGHT,
  for the portfolio date", and the reason the price-of-local-ordering
  constants are measured against the true optimum.

  Proof shape (capacity counting only):
  * Stage 1 (concrete model, CapacityBound.lean): on any machine, the
    jobs it completes by time `a` carry total work ≤ k·a
    (`capacity_at_time`, the set form of the paper's capacity lemma).
    Applied on a machine attaining job M's availability a = r M, with
    M among the completed jobs, the OTHER released work is ≤ k·a − w M.
  * Stage 2 is abstracted by `Downstream`: a cumulative progress
    function `done t j` that (i) never exceeds w j, (ii) is zero
    until the job's release, (iii) grows at total rate ≤ k. Every
    physical stage-2 execution — any discipline, preemptive or not,
    work-conserving or not — satisfies these axioms, so the lower
    bound holds for ALL of them.
  * Arithmetic: work finished by a is ≤ k·a − w M; the rest is done
    at rate ≤ k after a.

  All statements are over ℕ (integer work units and time steps),
  matching the rest of the development; inequalities are kept in
  additive form to avoid truncated subtraction.
-/

import AssemblyFlowShop.CapacityBound
import Mathlib.Tactic

namespace MakespanLowerBound

open CapacityBound

variable {n k : ℕ}

/-! ## Stage 1: the capacity bound at a time, in set form -/

/-- **Capacity of one concrete machine, set form.** The jobs a
    machine completes by time `a` carry total work at most `k·a`.
    (`capacity_bound_concrete` is the positional form of this fact;
    here we need it for the sublevel set of an arbitrary time.) -/
theorem capacity_at_time (σ : Equiv.Perm (Fin n)) (d : Fin n → Fin k → ℕ)
    (a : ℕ) :
    ∑ j ∈ Finset.univ.filter (fun j => completionTime σ d j ≤ a),
      (∑ ℓ, d j ℓ) ≤ k * a := by
  set S : Finset (Fin n) :=
    Finset.univ.filter (fun j => completionTime σ d j ≤ a) with hS
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]
  -- Positions occupied by the jobs of S, and the latest one.
  set P : Finset (Fin n) := S.image (fun j => σ.symm j) with hP
  have hPne : P.Nonempty := hSne.image _
  set pstar : Fin n := P.max' hPne with hpstar
  have hpstar_mem : pstar ∈ P := P.max'_mem hPne
  obtain ⟨jstar, hjstar_mem, hjstar_eq⟩ := Finset.mem_image.mp hpstar_mem
  have h_sigma_pstar : σ pstar = jstar := by
    rw [← hjstar_eq]; exact σ.apply_symm_apply jstar
  have hjstar_le : completionTime σ d jstar ≤ a := by
    have := hjstar_mem
    rw [hS, Finset.mem_filter] at this
    exact this.2
  -- Per worker, the portions of S-jobs sit at positions ≤ p*,
  -- so they are part of the worker's finish time there.
  have h_per_worker : ∀ ℓ : Fin k, (∑ j ∈ S, d j ℓ) ≤ a := by
    intro ℓ
    have h_reindex : (∑ j ∈ S, d j ℓ) = ∑ p ∈ P, d (σ p) ℓ := by
      rw [hP, Finset.sum_image (by
        intro x _ y _ hxy
        exact σ.symm.injective hxy)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [σ.apply_symm_apply]
    calc (∑ j ∈ S, d j ℓ)
        = ∑ p ∈ P, d (σ p) ℓ := h_reindex
      _ ≤ ∑ p ∈ Finset.Iic pstar, d (σ p) ℓ := by
          apply Finset.sum_le_sum_of_subset
          intro p hp
          exact Finset.mem_Iic.mpr (P.le_max' p hp)
      _ = finishTime σ d ℓ pstar := rfl
      _ ≤ completionTime σ d (σ pstar) :=
          finishTime_le_completionTime σ d ℓ pstar
      _ = completionTime σ d jstar := by rw [h_sigma_pstar]
      _ ≤ a := hjstar_le
  calc ∑ j ∈ S, (∑ ℓ, d j ℓ)
      = ∑ ℓ, (∑ j ∈ S, d j ℓ) := Finset.sum_comm
    _ ≤ ∑ _ℓ : Fin k, a := Finset.sum_le_sum (fun ℓ _ => h_per_worker ℓ)
    _ = k * a := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ## Stage 2: an over-approximating downstream abstraction -/

/-- A downstream (assembly-stage) execution, abstracted by its
    cumulative progress function: `done t j` is the amount of job
    `j`'s stage-2 work completed by time `t`. The axioms hold for
    every physical execution with `k` unit-rate workers and release
    dates `r` — any discipline, preemptive or not, work-conserving or
    not — so lower bounds proved from them apply universally. -/
structure Downstream (n k : ℕ) (w r : Fin n → ℕ) where
  /-- Cumulative stage-2 work of job `j` completed by time `t`. -/
  done : ℕ → Fin n → ℕ
  /-- Completed work never exceeds the job's stage-2 work. -/
  done_le : ∀ t j, done t j ≤ w j
  /-- Nothing is completed before the job's release. -/
  gated : ∀ t j, t ≤ r j → done t j = 0
  /-- Total completed work grows at rate at most `k`
      (additive form, avoiding truncated subtraction). -/
  capacity : ∀ t₁ t₂ : ℕ, t₁ ≤ t₂ →
    (∑ j, done t₂ j) ≤ (∑ j, done t₁ j) + k * (t₂ - t₁)
  /-- The makespan: a time by which everything is complete. -/
  T : ℕ
  /-- By time `T` every job is fully processed. -/
  complete : ∀ j, done T j = w j

/-- **Abstract downstream lower bound.** If the total work of the
    jobs released by time `r M` is within machine capacity `k · r M`
    (the stage-1 capacity fact), then `k · T ≥ W + w M`. -/
theorem downstream_lower_bound (w r : Fin n → ℕ)
    (D : Downstream n k w r) (M : Fin n)
    (h_avail : ∑ j ∈ Finset.univ.filter (fun j => r j ≤ r M), w j
      ≤ k * r M) :
    (∑ j, w j) + w M ≤ k * D.T := by
  set a : ℕ := r M with ha
  by_cases haT : a ≤ D.T
  · -- Main case. Step 1: work completed by time a, plus w M, fits in k·a.
    set F : Finset (Fin n) := Finset.univ.filter (fun j => r j ≤ a) with hF
    have hMF : M ∈ F := by
      rw [hF, Finset.mem_filter]
      exact ⟨Finset.mem_univ M, le_of_eq ha.symm⟩
    have h_unreleased : ∀ j ∈ Finset.univ.filter (fun j => ¬ r j ≤ a),
        D.done a j = 0 := by
      intro j hj
      rw [Finset.mem_filter] at hj
      exact D.gated a j (le_of_lt (lt_of_not_ge hj.2))
    have h_split : (∑ j, D.done a j) = ∑ j ∈ F, D.done a j := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j => r j ≤ a) (D.done a), hF]
      rw [Finset.sum_eq_zero h_unreleased, add_zero]
    have h_doneM : D.done a M = 0 := D.gated a M (le_of_eq ha.symm)
    have h_step1 : (∑ j, D.done a j) + w M ≤ k * a := by
      have h_erase : (∑ j ∈ F, D.done a j)
          = ∑ j ∈ F.erase M, D.done a j := by
        rw [← Finset.sum_erase_add F _ hMF, h_doneM, add_zero]
      have h_le_w : (∑ j ∈ F.erase M, D.done a j)
          ≤ ∑ j ∈ F.erase M, w j :=
        Finset.sum_le_sum (fun j _ => D.done_le a j)
      calc (∑ j, D.done a j) + w M
          = (∑ j ∈ F.erase M, D.done a j) + w M := by
            rw [h_split, h_erase]
        _ ≤ (∑ j ∈ F.erase M, w j) + w M := by
            exact Nat.add_le_add_right h_le_w _
        _ = ∑ j ∈ F, w j := Finset.sum_erase_add F w hMF
        _ ≤ k * a := h_avail
    -- Step 2: everything else is processed at rate ≤ k after a.
    have h_step2 : (∑ j, w j) ≤ (∑ j, D.done a j) + k * (D.T - a) := by
      have := D.capacity a (D.T) haT
      simpa [D.complete] using this
    -- Combine.
    calc (∑ j, w j) + w M
        ≤ ((∑ j, D.done a j) + k * (D.T - a)) + w M :=
          Nat.add_le_add_right h_step2 _
      _ = ((∑ j, D.done a j) + w M) + k * (D.T - a) := by ring
      _ ≤ k * a + k * (D.T - a) := Nat.add_le_add_right h_step1 _
      _ = k * (a + (D.T - a)) := by ring
      _ = k * D.T := by rw [Nat.add_sub_cancel' haT]
  · -- Degenerate case T < a: then M was never released before T,
    -- so w M = 0 and the plain capacity bound from time 0 suffices.
    have hTa : D.T ≤ a := le_of_lt (lt_of_not_ge haT)
    have h_wM : w M = 0 := by
      have := D.gated (D.T) M (ha ▸ hTa)
      rw [D.complete M] at this
      exact this
    have h_zero : (∑ j, D.done 0 j) = 0 :=
      Finset.sum_eq_zero (fun j _ => D.gated 0 j (Nat.zero_le _))
    have h_cap := D.capacity 0 (D.T) (Nat.zero_le _)
    rw [h_zero, zero_add, Nat.sub_zero] at h_cap
    have h_W : (∑ j, w j) ≤ k * D.T := by
      calc (∑ j, w j) = ∑ j, D.done (D.T) j := by
            exact (Finset.sum_congr rfl (fun j _ => (D.complete j).symm))
        _ ≤ k * D.T := h_cap
    rw [h_wM, add_zero]
    exact h_W

/-! ## The combined two-stage theorem -/

/-- **The universal makespan lower bound (Theorem S1(a)).**

    Homogeneous model: `m` concrete stage-1 machines (orders `σ i`,
    divisions `d i`, each summing to the common works `w`); release
    dates are the assembly availabilities `r j = max_i C_i j`; the
    downstream stage is ANY execution satisfying the `Downstream`
    axioms. Then for EVERY job `M`:

        (Σ_j w j) + w M ≤ k · T.

    With `M` a maximum-work job this is k·Cmax ≥ W + w_max; the
    synchronized schedule attains it, so the synchronized makespan is
    the exact optimum regardless of the shared order. -/
theorem two_stage_makespan_lower_bound {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Equiv.Perm (Fin n)) (d : Fin m → Fin n → Fin k → ℕ)
    (w : Fin n → ℕ)
    (h_work : ∀ i j, (∑ ℓ, d i j ℓ) = w j)
    (r : Fin n → ℕ)
    (h_r : ∀ j, r j = Finset.univ.sup
      (fun i => completionTime (σ i) (d i) j))
    (D : Downstream n k w r) (M : Fin n) :
    (∑ j, w j) + w M ≤ k * D.T := by
  -- Any machine serves: every job's completion on it is at most the
  -- availability sup. (The prose argument picks the machine finishing
  -- M last; the formal proof shows that choice is unnecessary.)
  set istar : Fin m := ⟨0, hm⟩ with histar
  -- Every job's completion on machine i* is at most its availability.
  have h_C_le_r : ∀ j, completionTime (σ istar) (d istar) j ≤ r j := by
    intro j
    rw [h_r j]
    exact Finset.le_sup (f := fun i => completionTime (σ i) (d i) j)
      (Finset.mem_univ istar)
  -- Jobs released by r M are completed by r M on machine i*.
  have h_subset :
      Finset.univ.filter (fun j => r j ≤ r M) ⊆
      Finset.univ.filter
        (fun j => completionTime (σ istar) (d istar) j ≤ r M) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, le_trans (h_C_le_r j) hj.2⟩
  -- The stage-1 capacity fact at time r M, in the common works w.
  have h_avail : ∑ j ∈ Finset.univ.filter (fun j => r j ≤ r M), w j
      ≤ k * r M := by
    calc ∑ j ∈ Finset.univ.filter (fun j => r j ≤ r M), w j
        ≤ ∑ j ∈ Finset.univ.filter
            (fun j => completionTime (σ istar) (d istar) j ≤ r M), w j := by
          apply Finset.sum_le_sum_of_subset h_subset
      _ = ∑ j ∈ Finset.univ.filter
            (fun j => completionTime (σ istar) (d istar) j ≤ r M),
            (∑ ℓ, d istar j ℓ) :=
          Finset.sum_congr rfl (fun j _ => (h_work istar j).symm)
      _ ≤ k * r M := capacity_at_time (σ istar) (d istar) (r M)
  exact downstream_lower_bound w r D M h_avail

/-- The headline form: `k·Cmax ≥ W + w_max`. -/
theorem two_stage_makespan_lower_bound_max {m : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (σ : Fin m → Equiv.Perm (Fin n)) (d : Fin m → Fin n → Fin k → ℕ)
    (w : Fin n → ℕ)
    (h_work : ∀ i j, (∑ ℓ, d i j ℓ) = w j)
    (r : Fin n → ℕ)
    (h_r : ∀ j, r j = Finset.univ.sup
      (fun i => completionTime (σ i) (d i) j))
    (D : Downstream n k w r) :
    (∑ j, w j) + Finset.univ.sup w ≤ k * D.T := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨M, _, hM⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) w
      Finset.univ_nonempty
  have hsup : Finset.univ.sup w = w M :=
    le_antisymm
      (Finset.sup_le (fun j _ => hM j (Finset.mem_univ j)))
      (Finset.le_sup (Finset.mem_univ M))
  rw [hsup]
  exact two_stage_makespan_lower_bound hm σ d w h_work r h_r D M

end MakespanLowerBound
