import OptimalG.FineGridRealization

/-! # Exact running-minimum geometry for a block of zero-height candidates -/

namespace OptimalG
open scoped BigOperators

/-- Once the first zero-height candidate is encountered, the running minimum
is zero. Every preceding height is one. -/
theorem runningMin_first_zero {m : ℕ} [NeZero m]
    (order : Equiv.Perm (Fin m)) (rho : Fin m → ℝ) (q : Fin m)
    (hnonneg : ∀ x, 0 ≤ rho x)
    (hbefore : ∀ i : Fin m, i.val < q.val → rho (order i) = 1)
    (hzero : rho (order q) = 0) (i : Fin m) :
    runningMin (fun x => (order.symm x).val) rho (order i) =
      if i.val < q.val then 1 else 0 := by
  by_cases hi : i.val < q.val
  · rw [if_pos hi]
    apply le_antisymm
    · simpa only [hbefore i hi] using runningMin_le_self (fun x => (order.symm x).val) rho (order i)
    · apply Finset.le_inf'
      intro x _
      split_ifs with hxi
      · simp only [Equiv.symm_apply_apply] at hxi
        have hx : (order.symm x).val < q.val := lt_of_le_of_lt hxi hi
        simpa only [Equiv.apply_symm_apply] using (hbefore (order.symm x) hx).ge
      · exact (hbefore i hi).ge
  · rw [if_neg hi]
    apply le_antisymm
    · have h := runningMin_le_of_rank_le (fun x => (order.symm x).val) rho (order i) (order q)
        (by simpa only [Equiv.symm_apply_apply] using Nat.le_of_not_gt hi)
      simpa only [hzero] using h
    · exact runningMin_nonneg _ rho hnonneg _

theorem first_zero_uniform_cost {m : ℕ} [NeZero m]
    (order : Equiv.Perm (Fin m)) (rho : Fin m → ℝ) (q : Fin m)
    (hnonneg : ∀ x, 0 ≤ rho x)
    (hbefore : ∀ i : Fin m, i.val < q.val → rho (order i) = 1)
    (hzero : rho (order q) = 0) :
    expectation (uniformVector m) (runningMin (fun x => (order.symm x).val) rho) =
      (q.val : ℝ) / m := by
  unfold expectation
  rw [← Equiv.sum_comp order]
  simp_rw [runningMin_first_zero order rho q hnonneg hbefore hzero]
  have heq : ∀ i : Fin m, uniformVector m (order i) * (if i.val < q.val then 1 else 0) =
      if i.val < q.val then 1 / (m : ℝ) else 0 := by
    intro i
    split_ifs <;> simp [uniformVector]
  simp_rw [heq]
  change rankCut (fun _ : Fin m => 1 / (m : ℝ)) q.val = _
  rw [rankCut_const _ _ q.isLt.le]
  ring

theorem first_zero_gap_le_one {m : ℕ} [NeZero m]
    (order : Equiv.Perm (Fin m)) (rho : Fin m → ℝ)
    (hnonneg : ∀ x, 0 ≤ rho x) (hupper : ∀ x, rho x ≤ 1) :
    maximumGap (fun x => (order.symm x).val) rho ≤ 1 := by
  apply Finset.sup'_le
  intro x _
  have hm := runningMin_nonneg (fun x => (order.symm x).val) rho hnonneg x
  linarith [hupper x]

theorem first_zero_gap_eq_one {m : ℕ} [NeZero m]
    (order : Equiv.Perm (Fin m)) (rho : Fin m → ℝ) (q : Fin m)
    (hnonneg : ∀ x, 0 ≤ rho x) (hupper : ∀ x, rho x ≤ 1)
    (hbefore : ∀ i : Fin m, i.val < q.val → rho (order i) = 1)
    (hzero : rho (order q) = 0) (j : Fin m) (hqj : q.val ≤ j.val)
    (hone : rho (order j) = 1) :
    maximumGap (fun x => (order.symm x).val) rho = 1 := by
  apply le_antisymm (first_zero_gap_le_one order rho hnonneg hupper)
  have h := le_maximumGap (fun x => (order.symm x).val) rho (order j)
  rw [runningMin_first_zero order rho q hnonneg hbefore hzero, if_neg (not_lt.mpr hqj), hone,
    sub_zero] at h
  exact h

theorem first_zero_gap_eq_zero {m : ℕ} [NeZero m]
    (order : Equiv.Perm (Fin m)) (rho : Fin m → ℝ) (q : Fin m)
    (hnonneg : ∀ x, 0 ≤ rho x)
    (hbefore : ∀ i : Fin m, i.val < q.val → rho (order i) = 1)
    (hafter : ∀ i : Fin m, q.val ≤ i.val → rho (order i) = 0) :
    maximumGap (fun x => (order.symm x).val) rho = 0 := by
  apply le_antisymm _ (maximumGap_nonneg _ _)
  apply Finset.sup'_le
  intro x _
  obtain ⟨i, rfl⟩ := order.surjective x
  rw [runningMin_first_zero order rho q hnonneg hbefore (hafter q le_rfl)]
  split_ifs with hi
  · rw [hbefore i hi]; norm_num
  · rw [hafter i (Nat.le_of_not_gt hi)]; norm_num

end OptimalG
