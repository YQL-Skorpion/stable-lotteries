import OptimalG.OneReferenceOrder
import OptimalG.BiasedMetric

/-! # Exact running minima after inserting a zero-height reference -/

namespace OptimalG
open scoped BigOperators

theorem extendZeroWeight_nonneg {m : ℕ} (rho : Fin m → ℝ) (hrho : ∀ a, 0 ≤ rho a) :
    ∀ a, 0 ≤ extendZeroWeight rho a := by
  intro a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp
  · simpa using hrho i

/-- Before the inserted reference, the supported running minimum is unchanged;
after it, the running minimum is zero. -/
theorem runningMin_insertReference {m : ℕ} [NeZero m] (k : Fin (m + 1))
    (order : Equiv.Perm (Fin m)) (rho : Fin m → ℝ) (hrho : ∀ a, 0 ≤ rho a) (i : Fin m) :
    runningMin (fun a => ((insertReferenceOrder k order).symm a).val)
      (extendZeroWeight rho) (order i).castSucc =
      if i.val < k.val then runningMin (fun a => (order.symm a).val) rho (order i) else 0 := by
  let fullRank := fun a => ((insertReferenceOrder k order).symm a).val
  have hrank (a : Fin m) : fullRank a.castSucc = (k.succAbove (order.symm a)).val := by
    simp [fullRank]
  have href : fullRank (Fin.last m) = k.val := by simp [fullRank]
  have horder : fullRank (order i).castSucc = (k.succAbove i).val := by simp [fullRank]
  have hbefore : (k.succAbove i).val < k.val ↔ i.val < k.val := Fin.succAbove_lt_iff_castSucc_lt k i
  change runningMin fullRank (extendZeroWeight rho) (order i).castSucc = _
  by_cases hi : i.val < k.val
  · rw [if_pos hi]
    apply le_antisymm
    · obtain ⟨a, ha, hmin⟩ := runningMin_attained (fun a => (order.symm a).val) rho (order i)
      rw [Equiv.symm_apply_apply] at ha
      rw [hmin]
      have haFull : fullRank a.castSucc ≤ fullRank (order i).castSucc := by
        rw [hrank, horder]
        exact (Fin.succAbove_le_succAbove_iff).mpr ha
      simpa only [extendZeroWeight_castSucc] using
        runningMin_le_of_rank_le fullRank (extendZeroWeight rho) (order i).castSucc a.castSucc haFull
    · apply Finset.le_inf'
      intro a _
      refine Fin.lastCases ?_ (fun x => ?_) a
      · rw [if_neg (by rw [href, horder]; exact not_le.mpr (hbefore.mpr hi)), extendZeroWeight_castSucc]
        exact runningMin_le_self _ rho _
      · split_ifs with hx
        · rw [hrank, horder] at hx
          have hxi : (order.symm x).val ≤ i.val := Fin.succAbove_le_succAbove_iff.mp hx
          simp only [extendZeroWeight_castSucc]
          apply runningMin_le_of_rank_le
          simpa only [Equiv.symm_apply_apply] using hxi
        · simp only [extendZeroWeight_castSucc]
          exact runningMin_le_self _ rho _
  · rw [if_neg hi]
    apply le_antisymm
    · have hki : fullRank (Fin.last m) ≤ fullRank (order i).castSucc := by
        rw [href, horder]
        exact not_lt.mp (fun h => hi (hbefore.mp h))
      simpa only [extendZeroWeight_last] using
        runningMin_le_of_rank_le fullRank (extendZeroWeight rho) (order i).castSucc (Fin.last m) hki
    · exact runningMin_nonneg _ _ (extendZeroWeight_nonneg rho hrho) _

theorem insertReference_runningMin_cost {m : ℕ} [NeZero m] (k : Fin (m + 1))
    (order : Equiv.Perm (Fin m)) (rho D : Fin m → ℝ) (hrho : ∀ a, 0 ≤ rho a) :
    expectation (extendZeroWeight D)
      (runningMin (fun a => ((insertReferenceOrder k order).symm a).val) (extendZeroWeight rho)) =
      rankCut (fun i => D (order i) * runningMin (fun a => (order.symm a).val) rho (order i)) k.val := by
  unfold expectation
  rw [Fin.sum_univ_castSucc]
  simp only [extendZeroWeight_last, zero_mul, add_zero, extendZeroWeight_castSucc]
  rw [← Equiv.sum_comp order]
  simp_rw [runningMin_insertReference k order rho hrho]
  unfold rankCut
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  split_ifs <;> ring

theorem insertReference_gap_le {m : ℕ} [NeZero m] (k : Fin (m + 1))
    (order : Equiv.Perm (Fin m)) (rho : Fin m → ℝ) (hrho : ∀ a, 0 ≤ rho a)
    (B : ℝ) (hB : 0 ≤ B)
    (hgap : ∀ i : Fin m, rho (order i) -
      (if i.val < k.val then runningMin (fun a => (order.symm a).val) rho (order i) else 0) ≤ B) :
    maximumGap (fun a => ((insertReferenceOrder k order).symm a).val) (extendZeroWeight rho) ≤ B := by
  apply Finset.sup'_le
  intro a _
  refine Fin.lastCases ?_ (fun x => ?_) a
  · rw [extendZeroWeight_last, runningMin_at_zero _ _ (extendZeroWeight_nonneg rho hrho) _ (by simp)]
    simpa using hB
  · obtain ⟨i, rfl⟩ := order.surjective x
    rw [extendZeroWeight_castSucc, runningMin_insertReference k order rho hrho]
    exact hgap i

end OptimalG
