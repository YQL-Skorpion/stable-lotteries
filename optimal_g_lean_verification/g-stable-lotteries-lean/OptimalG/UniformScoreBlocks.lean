import OptimalG.FineGridRealization

/-! # Exact primitive sums over finite uniform rank blocks -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

theorem uniform_mass_activation {m : ℕ} [NeZero m] (g : ℝ → ℝ) (hg : Continuous g)
    (order : Equiv.Perm (Fin m)) (i : Fin m) :
    (1 / (m : ℝ)) * orderedActivation g (uniformVector m) order (order i) =
      activationPrimitive g (((i.val + 1 : ℕ) : ℝ) / m) -
        activationPrimitive g ((i.val : ℝ) / m) := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  rw [← scoreExtension_eq_orderedActivation g hg order (order i) (uniformVector m)
    (one_div_ne_zero hm)]
  unfold scoreExtension
  rw [rankPrefixLinear_apply]
  simp only [uniformVector, Equiv.symm_apply_apply]
  rw [rankCut_const _ _ i.isLt.le]
  have hleft : (i.val : ℝ) * (1 / m) = (i.val : ℝ) / m := by ring
  have hright : (i.val : ℝ) * (1 / m) + 1 / m = ((i.val + 1 : ℕ) : ℝ) / m := by push_cast; ring
  rw [hleft, ← hleft, hright]
  rw [hleft]
  exact mul_div_cancel₀ _ (one_div_ne_zero hm)

/-- Prefix summation is literal finite telescoping of adjacent rank intervals. -/
theorem uniform_activation_prefix {m : ℕ} [NeZero m] (g : ℝ → ℝ) (hg : Continuous g)
    (order : Equiv.Perm (Fin m)) (k : ℕ) (hk : k ≤ m) :
    rankCut (fun i => (1 / (m : ℝ)) * orderedActivation g (uniformVector m) order (order i)) k =
      activationPrimitive g ((k : ℝ) / m) := by
  induction k with
  | zero => simp [activationPrimitive]
  | succ k ih =>
    have hkm : k < m := by omega
    rw [rankCut_succ _ ⟨k, hkm⟩, ih (by omega), uniform_mass_activation g hg order ⟨k, hkm⟩]
    ring

theorem rankCut_interval_difference {m : ℕ} (f : Fin m → ℝ) (k l : ℕ) (hkl : k ≤ l) :
    (∑ i : Fin m, if k ≤ i.val ∧ i.val < l then f i else 0) = rankCut f l - rankCut f k := by
  simp only [rankCut, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> first | omega | ring

theorem uniform_activation_block {m : ℕ} [NeZero m] (g : ℝ → ℝ) (hg : Continuous g)
    (order : Equiv.Perm (Fin m)) (k l : ℕ) (hkl : k ≤ l) (hlm : l ≤ m) :
    (∑ i : Fin m, if k ≤ i.val ∧ i.val < l then
      (1 / (m : ℝ)) * orderedActivation g (uniformVector m) order (order i) else 0) =
      activationPrimitive g ((l : ℝ) / m) - activationPrimitive g ((k : ℝ) / m) := by
  rw [rankCut_interval_difference _ k l hkl,
    uniform_activation_prefix g hg order l hlm, uniform_activation_prefix g hg order k (hkl.trans hlm)]

/-- The high class is the complement of the contiguous middle zero block. -/
theorem uniform_high_class_activation {m : ℕ} [NeZero m] (g : ℝ → ℝ) (hg : Continuous g)
    (order : Equiv.Perm (Fin m)) (rho : Fin m → ℝ) (k l : ℕ)
    (hkl : k ≤ l) (hlm : l ≤ m)
    (hshape : ∀ i, rho (order i) = if i.val < k ∨ l ≤ i.val then 1 else 0) :
    expectation (uniformVector m) (fun x => rho x * orderedActivation g (uniformVector m) order x) =
      activationPrimitive g 1 -
        (activationPrimitive g ((l : ℝ) / m) - activationPrimitive g ((k : ℝ) / m)) := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hpoint : ∀ i : Fin m,
      uniformVector m (order i) * (rho (order i) * orderedActivation g (uniformVector m) order (order i)) =
      (1 / (m : ℝ)) * orderedActivation g (uniformVector m) order (order i) -
        (if k ≤ i.val ∧ i.val < l then
          (1 / (m : ℝ)) * orderedActivation g (uniformVector m) order (order i) else 0) := by
    intro i
    rw [hshape]
    dsimp [uniformVector]
    split_ifs <;> first | omega | ring
  unfold expectation
  rw [← Equiv.sum_comp order]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, uniform_activation_block g hg order k l hkl hlm]
  have htotal := uniform_activation_prefix g hg order m le_rfl
  simp only [rankCut, Fin.isLt, if_true, div_self hm] at htotal
  rw [htotal]

end OptimalG
