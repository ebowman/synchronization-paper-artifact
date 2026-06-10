/-
  The Capacity Bound from the Concrete Machine Model
  ====================================================

  Earlier files (WaterFilling.lean) take the capacity bound
  W_i(s) ≤ k · r(π(s)) as a hypothesis. This file DERIVES it from
  a concrete model of one stage-1 machine:

  - k workers, n jobs;
  - the machine processes jobs in an arbitrary order σ (a bijection
    from positions to jobs);
  - worker ℓ receives d j ℓ units of job j, processes its portions
    back-to-back in position order, so its cumulative finish time
    after position p is F ℓ p = Σ_{t ≤ p} d (σ t) ℓ;
  - the completion time of job j is C j = max over workers of
    F ℓ (position of j);
  - r j is any upper bound on C j (in the full model, r j is the
    max of C_i j over all machines i, hence an upper bound for
    each single machine).

  Main result (`capacity_bound_concrete`): if π orders jobs by
  non-decreasing r, then for every position s the total work of
  jobs π(0..s) on this machine is at most k * r (π s).

  The proof is the paper's argument made precise:
  every portion of every job in {π 0, …, π s} is finished by its
  job's completion time ≤ r (π s); per worker, the portions of
  those jobs are among the first p* positions, where p* is the
  latest machine position occupied by a job of the set; the
  worker's cumulative work through p* is F ℓ p* ≤ C (σ p*) ≤
  r (π s); summing over the k workers gives the bound.

  Combined with `ceil_div_le_of_le_mul` (WaterFilling.lean) this
  closes the gap between the abstract dominance theorems and the
  concrete schedule model.
-/

import AssemblyFlowShop.WaterFilling
import Mathlib.Tactic

namespace CapacityBound

variable {n k : ℕ}

/-- Cumulative finish time of worker `ℓ` after machine position `p`:
    the total work assigned to `ℓ` among the jobs at positions `0..p`
    of the machine order `σ`. Workers process their portions
    back-to-back starting at time 0, so cumulative work equals
    elapsed time. -/
def finishTime (σ : Equiv.Perm (Fin n)) (d : Fin n → Fin k → ℕ)
    (ℓ : Fin k) (p : Fin n) : ℕ :=
  ∑ t ∈ Finset.Iic p, d (σ t) ℓ

/-- Completion time of job `j` on the machine: the latest finish
    time among all workers at `j`'s position. (Workers assigned no
    work on `j` are included; this matches the paper's definition
    of completion times and only makes the completion time, and
    hence the bound proved here, larger.) -/
def completionTime (σ : Equiv.Perm (Fin n)) (d : Fin n → Fin k → ℕ)
    (j : Fin n) : ℕ :=
  Finset.univ.sup (fun ℓ => finishTime σ d ℓ (σ.symm j))

/-- `finishTime` is monotone in the position. -/
lemma finishTime_mono (σ : Equiv.Perm (Fin n)) (d : Fin n → Fin k → ℕ)
    (ℓ : Fin k) {p p' : Fin n} (h : p ≤ p') :
    finishTime σ d ℓ p ≤ finishTime σ d ℓ p' := by
  unfold finishTime
  exact Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr h)

/-- Each worker's finish time at a position is at most the completion
    time of the job at that position. -/
lemma finishTime_le_completionTime (σ : Equiv.Perm (Fin n))
    (d : Fin n → Fin k → ℕ) (ℓ : Fin k) (p : Fin n) :
    finishTime σ d ℓ p ≤ completionTime σ d (σ p) := by
  unfold completionTime
  have h : σ.symm (σ p) = p := σ.symm_apply_apply p
  rw [h]
  exact Finset.le_sup (f := fun ℓ => finishTime σ d ℓ p) (Finset.mem_univ ℓ)

/-- **The capacity bound, derived from the concrete model
    (the paper's capacity lemma, for one machine).**

    Hypotheses:
    - `σ` is the machine's processing order, `d` its work division;
    - `r` dominates this machine's completion times (in the full
      model `r j = max_i C_i j`, so this holds for every machine);
    - `π` sorts jobs by non-decreasing `r`.

    Conclusion: for every position `s`, the total work of jobs
    `π 0, …, π s` on this machine is at most `k * r (π s)`. -/
theorem capacity_bound_concrete
    (σ π : Equiv.Perm (Fin n)) (d : Fin n → Fin k → ℕ) (r : Fin n → ℕ)
    (h_release : ∀ j, completionTime σ d j ≤ r j)
    (h_sorted : ∀ t t' : Fin n, t ≤ t' → r (π t) ≤ r (π t'))
    (s : Fin n) :
    ∑ t ∈ Finset.Iic s, (∑ ℓ, d (π t) ℓ) ≤ k * r (π s) := by
  -- The machine positions occupied by jobs π 0, …, π s.
  set P : Finset (Fin n) := (Finset.Iic s).image (fun t => σ.symm (π t)) with hP
  have hP_nonempty : P.Nonempty :=
    ⟨σ.symm (π s), Finset.mem_image_of_mem _ (Finset.mem_Iic.mpr le_rfl)⟩
  -- p* := the latest such position.
  set pstar : Fin n := P.max' hP_nonempty with hpstar
  have hpstar_mem : pstar ∈ P := P.max'_mem hP_nonempty
  -- The job at position p* is some π t* with t* ≤ s.
  obtain ⟨tstar, htstar_mem, htstar_eq⟩ := Finset.mem_image.mp hpstar_mem
  have htstar_le : tstar ≤ s := Finset.mem_Iic.mp htstar_mem
  -- σ p* = π t*, so C (σ p*) ≤ r (π t*) ≤ r (π s).
  have h_sigma_pstar : σ pstar = π tstar := by
    rw [← htstar_eq]; exact σ.apply_symm_apply (π tstar)
  -- Step 1: per worker, the work on jobs π 0..π s is ≤ F ℓ p*.
  have h_per_worker : ∀ ℓ : Fin k,
      (∑ t ∈ Finset.Iic s, d (π t) ℓ) ≤ finishTime σ d ℓ pstar := by
    intro ℓ
    -- Reindex the sum over jobs by their machine positions.
    have h_reindex : (∑ t ∈ Finset.Iic s, d (π t) ℓ)
        = ∑ p ∈ P, d (σ p) ℓ := by
      rw [hP]
      rw [Finset.sum_image (by
        intro a _ b _ hab
        exact π.injective (σ.symm.injective hab))]
      congr 1
      ext t
      rw [σ.apply_symm_apply]
    rw [h_reindex]
    -- Those positions are all ≤ p*, so the sum is part of F ℓ p*.
    unfold finishTime
    apply Finset.sum_le_sum_of_subset
    intro p hp
    exact Finset.mem_Iic.mpr (P.le_max' p hp)
  -- Step 2: F ℓ p* ≤ C (σ p*) ≤ r (π t*) ≤ r (π s).
  have h_bound : ∀ ℓ : Fin k, (∑ t ∈ Finset.Iic s, d (π t) ℓ) ≤ r (π s) := by
    intro ℓ
    calc (∑ t ∈ Finset.Iic s, d (π t) ℓ)
        ≤ finishTime σ d ℓ pstar := h_per_worker ℓ
      _ ≤ completionTime σ d (σ pstar) := finishTime_le_completionTime σ d ℓ pstar
      _ = completionTime σ d (π tstar) := by rw [h_sigma_pstar]
      _ ≤ r (π tstar) := h_release (π tstar)
      _ ≤ r (π s) := h_sorted tstar s htstar_le
  -- Step 3: sum over the k workers.
  calc ∑ t ∈ Finset.Iic s, (∑ ℓ, d (π t) ℓ)
      = ∑ ℓ, (∑ t ∈ Finset.Iic s, d (π t) ℓ) := Finset.sum_comm
    _ ≤ ∑ _ℓ : Fin k, r (π s) := Finset.sum_le_sum (fun ℓ _ => h_bound ℓ)
    _ = k * r (π s) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **End-to-end: ceiling bound from the concrete model.**

    Composing the concrete capacity bound with
    `ceil_div_le_of_le_mul`: the water-filling completion time
    ⌈W_i(s)/k⌉ at each position is at most r (π s). This is the
    inequality used in the proof of the paper's main theorem. -/
theorem waterfill_release_le_concrete
    (hk : 0 < k)
    (σ π : Equiv.Perm (Fin n)) (d : Fin n → Fin k → ℕ) (r : Fin n → ℕ)
    (h_release : ∀ j, completionTime σ d j ≤ r j)
    (h_sorted : ∀ t t' : Fin n, t ≤ t' → r (π t) ≤ r (π t'))
    (s : Fin n) :
    ((∑ t ∈ Finset.Iic s, (∑ ℓ, d (π t) ℓ)) + k - 1) / k ≤ r (π s) :=
  ceil_div_le_of_le_mul _ k _ hk
    (capacity_bound_concrete σ π d r h_release h_sorted s)

/-- **End-to-end release-time domination for `m` machines.**

    Each machine `i` has its own order `σ i` and division `d i`;
    `r` dominates every machine's completion times (in the full model
    `r j = max_i C_i j`); `π` sorts jobs by non-decreasing `r`.

    The synchronized schedule processes jobs in order `π` on every
    machine and water-fills, achieving completion `⌈W_i(s)/k⌉` at
    position `s` on machine `i` (WaterFillAllocation.lean). Its
    release time for the job at position `s` — the max over machines
    of those completions — is at most `r (π s)`, the original
    release time. This is the inequality `r*_j ≤ r_j` in the proof
    of the paper's main theorem, derived here entirely from the
    concrete machine model. -/
theorem sync_release_le_concrete {m : ℕ}
    (hk : 0 < k)
    (σ : Fin m → Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin n))
    (d : Fin m → Fin n → Fin k → ℕ) (r : Fin n → ℕ)
    (h_release : ∀ i j, completionTime (σ i) (d i) j ≤ r j)
    (h_sorted : ∀ t t' : Fin n, t ≤ t' → r (π t) ≤ r (π t'))
    (s : Fin n) :
    Finset.univ.sup (fun i : Fin m =>
      ((∑ t ∈ Finset.Iic s, (∑ ℓ, d i (π t) ℓ)) + k - 1) / k) ≤ r (π s) := by
  apply Finset.sup_le
  intro i _
  exact waterfill_release_le_concrete hk (σ i) π (d i) r (h_release i) h_sorted s

end CapacityBound
