import OptimalG.ScoreDerivative
import OptimalG.ElectionOne

/-! # Inserting a zero-mass reference preserves every supported score -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

def extendZeroWeight {m : ℕ} (D : Fin m → ℝ) : Fin (m + 1) → ℝ := Fin.lastCases 0 D

@[simp] theorem extendZeroWeight_last {m : ℕ} (D : Fin m → ℝ) :
    extendZeroWeight D (Fin.last m) = 0 := by simp [extendZeroWeight]

@[simp] theorem extendZeroWeight_castSucc {m : ℕ} (D : Fin m → ℝ) (a : Fin m) :
    extendZeroWeight D a.castSucc = D a := by simp [extendZeroWeight]

noncomputable def extendZeroLottery {m : ℕ} (D : Lottery m) : Lottery (m + 1) where
  weight := extendZeroWeight D.weight
  nonneg a := by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp
    · simpa using D.nonneg i
  total := by simpa [Fin.sum_univ_castSucc] using D.total

def insertReferenceOrder {m : ℕ} (k : Fin (m + 1)) (order : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m + 1)) := (electionOneOrder k).trans (electionOneAction m order)

@[simp] theorem insertReferenceOrder_at {m : ℕ} (k : Fin (m + 1)) (order : Equiv.Perm (Fin m)) :
    insertReferenceOrder k order k = Fin.last m := by simp [insertReferenceOrder]

@[simp] theorem insertReferenceOrder_succAbove {m : ℕ} (k : Fin (m + 1))
    (order : Equiv.Perm (Fin m)) (i : Fin m) :
    insertReferenceOrder k order (k.succAbove i) = (order i).castSucc := by
  simp [insertReferenceOrder, electionOneOrder, finSuccEquiv'_succAbove, Fin.succAbove_last]

@[simp] theorem insertReferenceOrder_symm_last {m : ℕ} (k : Fin (m + 1)) (order : Equiv.Perm (Fin m)) :
    (insertReferenceOrder k order).symm (Fin.last m) = k :=
  (insertReferenceOrder k order).symm_apply_eq.mpr (insertReferenceOrder_at k order).symm

@[simp] theorem insertReferenceOrder_symm_castSucc {m : ℕ} (k : Fin (m + 1))
    (order : Equiv.Perm (Fin m)) (a : Fin m) :
    (insertReferenceOrder k order).symm a.castSucc = k.succAbove (order.symm a) := by
  apply (insertReferenceOrder k order).symm_apply_eq.mpr
  simp

/-- The supported prefix has exactly the same mass after inserting the
zero-mass reference, at any ordinal position. -/
theorem insertReference_prefix {m : ℕ} (k : Fin (m + 1)) (order : Equiv.Perm (Fin m))
    (D : Fin m → ℝ) (a : Fin m) :
    rankPrefixLinear (insertReferenceOrder k order) a.castSucc (extendZeroWeight D) =
      rankPrefixLinear order a D := by
  rw [rankPrefixLinear_apply, rankPrefixLinear_apply, insertReferenceOrder_symm_castSucc]
  unfold rankCut
  rw [Fin.sum_univ_succAbove _ k]
  simp only [insertReferenceOrder_at, extendZeroWeight_last, ite_self, zero_add,
    insertReferenceOrder_succAbove, extendZeroWeight_castSucc]
  apply Finset.sum_congr rfl
  intro i _
  have hiff : (k.succAbove i).val < (k.succAbove (order.symm a)).val ↔ i.val < (order.symm a).val :=
    Fin.succAbove_lt_succAbove_iff
  simp only [hiff]

theorem insertReference_scoreExtension {m : ℕ} (k : Fin (m + 1)) (order : Equiv.Perm (Fin m))
    (g : ℝ → ℝ) (D : Fin m → ℝ) (a : Fin m) :
    scoreExtension g (insertReferenceOrder k order) a.castSucc (extendZeroWeight D) =
      scoreExtension g order a D := by
  simp only [scoreExtension, insertReference_prefix, extendZeroWeight_castSucc]

theorem insertReference_supported_activation {m : ℕ} (k : Fin (m + 1)) (order : Equiv.Perm (Fin m))
    (g : ℝ → ℝ) (D : Fin m → ℝ) (a : Fin m) :
    orderedActivation g (extendZeroWeight D) (insertReferenceOrder k order) a.castSucc =
      orderedActivation g D order a := by
  unfold orderedActivation rankActivation
  simp only [Equiv.apply_symm_apply, extendZeroWeight_castSucc]
  rw [← rankPrefixLinear_apply, insertReference_prefix, rankPrefixLinear_apply]

theorem insertReference_reference_prefix {m : ℕ} (k : Fin (m + 1))
    (order : Equiv.Perm (Fin m)) (D : Fin m → ℝ) :
    rankPrefixLinear (insertReferenceOrder k order) (Fin.last m) (extendZeroWeight D) =
      rankCut (fun i => D (order i)) k.val := by
  rw [rankPrefixLinear_apply, insertReferenceOrder_symm_last]
  unfold rankCut
  rw [Fin.sum_univ_succAbove _ k]
  simp only [lt_self_iff_false, if_false, zero_add, insertReferenceOrder_succAbove,
    extendZeroWeight_castSucc]
  apply Finset.sum_congr rfl
  intro i _
  have hiff : (k.succAbove i).val < k.val ↔ i.val < k.val := Fin.succAbove_lt_iff_castSucc_lt k i
  simp only [hiff]

theorem insertReference_reference_activation {m : ℕ} (k : Fin (m + 1))
    (order : Equiv.Perm (Fin m)) (g : ℝ → ℝ) (D : Fin m → ℝ) :
    orderedActivation g (extendZeroWeight D) (insertReferenceOrder k order) (Fin.last m) =
      g (rankCut (fun i => D (order i)) k.val) := by
  unfold orderedActivation
  rw [rankActivation_of_mass_zero]
  · rw [← rankPrefixLinear_apply, insertReference_reference_prefix]
  · simp

end OptimalG
