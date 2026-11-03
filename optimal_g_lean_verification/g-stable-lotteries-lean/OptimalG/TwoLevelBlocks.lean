import OptimalG.BinaryRanking
import OptimalG.OneReferenceGeometry
import OptimalG.UniformScoreBlocks

/-! # Supported two-height blocks used in Election 3 -/

namespace OptimalG
open scoped BigOperators

def twoLevelHeight {m : ℕ} (z : ℕ) (a : Fin m) : ℝ := 2 - binaryHeight z a

theorem twoLevelHeight_bounds {m : ℕ} (z : ℕ) (a : Fin m) :
    1 ≤ twoLevelHeight z a ∧ twoLevelHeight z a ≤ 2 := by
  have h0 := binaryHeight_nonneg z a
  have h1 := binaryHeight_le_one z a
  dsimp [twoLevelHeight]
  constructor <;> linarith

theorem twoLevelHeight_nonneg {m : ℕ} (z : ℕ) (a : Fin m) : 0 ≤ twoLevelHeight z a :=
  le_trans (by norm_num) (twoLevelHeight_bounds z a).1

theorem runningMin_lower_bound {C : Type*} [Fintype C] [Nonempty C]
    (rank : C → ℕ) (rho : C → ℝ) (L : ℝ) (hL : ∀ a, L ≤ rho a) (a : C) :
    L ≤ runningMin rank rho a := by
  apply Finset.le_inf'
  intro b _
  split_ifs <;> apply hL

theorem runningMin_one_first {m : ℕ} [NeZero m]
    (order : Equiv.Perm (Fin m)) (rho : Fin m → ℝ)
    (hlower : ∀ a, 1 ≤ rho a) (hfirst : rho (order 0) = 1) (i : Fin m) :
    runningMin (fun a => (order.symm a).val) rho (order i) = 1 := by
  apply le_antisymm _ (runningMin_lower_bound _ rho 1 hlower _)
  have h := runningMin_le_of_rank_le (fun a => (order.symm a).val) rho (order i) (order 0)
    (by simp only [Equiv.symm_apply_apply, Fin.val_zero]; omega)
  simpa only [hfirst] using h

theorem runningMin_twoLevel_bottom {m : ℕ} [NeZero m]
    (order : Equiv.Perm (Fin m)) (rho : Fin m → ℝ) (h : ℕ)
    (hshape : ∀ i, rho (order i) = if i.val < h then 2 else 1) (i : Fin m) :
    runningMin (fun a => (order.symm a).val) rho (order i) = if i.val < h then 2 else 1 := by
  apply le_antisymm
  · simpa only [hshape] using runningMin_le_self (fun a => (order.symm a).val) rho (order i)
  · apply Finset.le_inf'
    intro a _
    obtain ⟨j, rfl⟩ := order.surjective a
    simp only [Equiv.symm_apply_apply, hshape]
    split_ifs <;> first | omega | norm_num

theorem twoLevel_block_shape (z h l : ℕ) (order : Equiv.Perm (Fin (z + h)))
    (hshape : ∀ i, binaryHeight z (order i) = if i.val < l ∨ l + h ≤ i.val then 1 else 0)
    (i : Fin (z + h)) :
    twoLevelHeight z (order i) = if l ≤ i.val ∧ i.val < l + h then 2 else 1 := by
  rw [twoLevelHeight, hshape]
  split_ifs <;> first | omega | norm_num

theorem twoLevel_middle_minimum (z h l : ℕ) [NeZero (z + h)]
    (hl : 0 < l) (order : Equiv.Perm (Fin (z + h)))
    (hshape : ∀ i, binaryHeight z (order i) = if i.val < l ∨ l + h ≤ i.val then 1 else 0)
    (i : Fin (z + h)) :
    runningMin (fun a => (order.symm a).val) (twoLevelHeight z) (order i) = 1 := by
  apply runningMin_one_first order (twoLevelHeight z) (fun a => (twoLevelHeight_bounds z a).1)
  rw [twoLevelHeight, hshape, Fin.val_zero, if_pos (Or.inl hl)]
  norm_num

theorem twoLevel_bottom_minimum (z h : ℕ) [NeZero (z + h)]
    (order : Equiv.Perm (Fin (z + h)))
    (hshape : ∀ i, binaryHeight z (order i) = if i.val < 0 ∨ 0 + h ≤ i.val then 1 else 0)
    (i : Fin (z + h)) :
    runningMin (fun a => (order.symm a).val) (twoLevelHeight z) (order i) =
      if i.val < h then 2 else 1 := by
  apply runningMin_twoLevel_bottom
  intro j
  rw [twoLevel_block_shape z h 0 order hshape]
  simp

theorem twoLevel_middle_cost (z h l : ℕ) [NeZero (z + h)]
    (hl : 0 < l) (order : Equiv.Perm (Fin (z + h)))
    (hshape : ∀ i, binaryHeight z (order i) = if i.val < l ∨ l + h ≤ i.val then 1 else 0)
    (k : Fin (z + h + 1)) :
    expectation (extendZeroWeight (uniformVector (z + h)))
      (runningMin (fun a => ((insertReferenceOrder k order).symm a).val)
        (extendZeroWeight (twoLevelHeight z))) = (k.val : ℝ) / (z + h : ℕ) := by
  rw [insertReference_runningMin_cost k order _ _ (twoLevelHeight_nonneg z)]
  simp_rw [twoLevel_middle_minimum z h l hl order hshape, mul_one]
  change rankCut (fun _ : Fin (z + h) => 1 / ((z + h : ℕ) : ℝ)) k.val = _
  rw [rankCut_const _ _ (by have := k.isLt; omega)]
  ring

theorem twoLevel_bottom_cost (z h : ℕ) [NeZero (z + h)]
    (order : Equiv.Perm (Fin (z + h)))
    (hshape : ∀ i, binaryHeight z (order i) = if i.val < 0 ∨ 0 + h ≤ i.val then 1 else 0)
    (k : Fin (z + h + 1)) (hkh : h ≤ k.val) :
    expectation (extendZeroWeight (uniformVector (z + h)))
      (runningMin (fun a => ((insertReferenceOrder k order).symm a).val)
        (extendZeroWeight (twoLevelHeight z))) = ((h : ℝ) + k.val) / (z + h : ℕ) := by
  rw [insertReference_runningMin_cost k order _ _ (twoLevelHeight_nonneg z)]
  simp_rw [twoLevel_bottom_minimum z h order hshape]
  have hpoint : ∀ i : Fin (z + h),
      (if i.val < k.val then uniformVector (z + h) (order i) * (if i.val < h then 2 else 1) else 0) =
      (if i.val < h then (1 : ℝ) / (z + h : ℕ) else 0) +
        (if i.val < k.val then (1 : ℝ) / (z + h : ℕ) else 0) := by
    intro i
    dsimp [uniformVector]
    split_ifs <;> first | omega | ring
  unfold rankCut
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  change rankCut (fun _ : Fin (z + h) => 1 / ((z + h : ℕ) : ℝ)) h +
    rankCut (fun _ : Fin (z + h) => 1 / ((z + h : ℕ) : ℝ)) k.val = _
  rw [rankCut_const _ _ (by omega), rankCut_const _ _ (by have := k.isLt; omega)]
  ring

end OptimalG
