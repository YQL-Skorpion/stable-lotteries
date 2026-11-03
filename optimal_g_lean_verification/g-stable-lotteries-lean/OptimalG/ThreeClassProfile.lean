import OptimalG.ClassWeightedProfile
import OptimalG.OneReferenceRealization
import OptimalG.TwoLevelGaps

/-! # Exact supported and reference scores for Election 3 block profiles -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

theorem block_middle_class_score (g : ℝ → ℝ) (hg : Continuous g)
    (z h l : ℕ) [NeZero (z + h)] (hl : l ≤ z)
    (order : Equiv.Perm (Fin (z + h)))
    (hshape : ∀ i, binaryHeight z (order i) = if i.val < l ∨ l + h ≤ i.val then 1 else 0) :
    expectation (uniformVector (z + h)) (fun a => binaryHeight z a *
      orderedActivation g (uniformVector (z + h)) order a) =
      ((z : ℝ) / (z + h : ℕ)) * activationPrimitive g 1 -
        (centeredPrimitive g ((l : ℝ) / (z + h : ℕ)) -
          centeredPrimitive g (((l + h : ℕ) : ℝ) / (z + h : ℕ))) := by
  rw [uniform_high_class_activation g hg order (binaryHeight z) l (l + h) (by omega) (by omega) hshape]
  have hm : ((z + h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (z + h)
  dsimp [centeredPrimitive]
  push_cast
  have hm' : (z : ℝ) + h ≠ 0 := by exact_mod_cast NeZero.ne (z + h)
  field_simp
  ring

/-- Balancing the high class's centered activation balances every candidate
after applying all actual within-class permutations. -/
theorem class_block_stationary {T : Type*} [Fintype T]
    (g : ℝ → ℝ) (hg : Continuous g) (z h : ℕ) (hz : 0 < z) (hh : 0 < h) [NeZero (z + h)]
    (l : T → ℕ) (hl : ∀ t, l t ≤ z) (orders : T → Equiv.Perm (Fin (z + h)))
    (hshape : ∀ t i, binaryHeight z (orders t i) = if i.val < l t ∨ l t + h ≤ i.val then 1 else 0)
    (w : T → ℝ) (hwsum : ∑ t, w t = 1)
    (hbalance : expectation w (fun t => centeredPrimitive g ((l t : ℝ) / (z + h : ℕ)) -
      centeredPrimitive g (((l t + h : ℕ) : ℝ) / (z + h : ℕ))) = 0) :
    ∀ a, expectation (typeProfileWeight w) (fun v => orderedActivation g (uniformVector (z + h))
      (classProfileOrder (binaryHeight z) orders v) a) = activationPrimitive g 1 := by
  apply classProfile_stationary z h hz hh g hg.continuousOn orders w hwsum
  simp_rw [block_middle_class_score g hg z h _ (hl _) _ (hshape _)]
  have he : expectation w (fun t => ((z : ℝ) / (z + h : ℕ)) * activationPrimitive g 1 -
      (centeredPrimitive g ((l t : ℝ) / (z + h : ℕ)) -
        centeredPrimitive g (((l t + h : ℕ) : ℝ) / (z + h : ℕ)))) =
      expectation w (fun _ => ((z : ℝ) / (z + h : ℕ)) * activationPrimitive g 1) -
        expectation w (fun t => centeredPrimitive g ((l t : ℝ) / (z + h : ℕ)) -
          centeredPrimitive g (((l t + h : ℕ) : ℝ) / (z + h : ℕ))) := by
    simp only [expectation, mul_sub, Finset.sum_sub_distrib]
  rw [he, hbalance, sub_zero, expectation_const hwsum]
  rfl

theorem classProfile_block_shape {T : Type*} (z h : ℕ)
    (l : T → ℕ) (orders : T → Equiv.Perm (Fin (z + h)))
    (hshape : ∀ t i, binaryHeight z (orders t i) = if i.val < l t ∨ l t + h ≤ i.val then 1 else 0)
    (v : T × heightStabilizer (binaryHeight (m := z + h) z)) (i : Fin (z + h)) :
    binaryHeight z (classProfileOrder (binaryHeight z) orders v i) =
      if i.val < l v.1 ∨ l v.1 + h ≤ i.val then 1 else 0 := by
  change binaryHeight z (v.2.val (orders v.1 i)) = _
  rw [v.2.property, hshape]

/-- At a uniform supported lottery, the unsupported reference activation is
exactly g(k/m), independently of within-class relabeling. -/
theorem classProfile_reference_average {T : Type*} [Fintype T]
    (g : ℝ → ℝ) (z h : ℕ) [NeZero (z + h)] (orders : T → Equiv.Perm (Fin (z + h)))
    (positions : T → Fin (z + h + 1)) (w : T → ℝ) :
    expectation (typeProfileWeight w) (fun v : T × heightStabilizer (binaryHeight (m := z + h) z) =>
      g (rankCut (fun i => uniformVector (z + h) (classProfileOrder (binaryHeight z) orders v i))
        (positions v.1).val)) = expectation w (fun t => g (((positions t).val : ℝ) / (z + h : ℕ))) := by
  have hpoint : ∀ v : T × heightStabilizer (binaryHeight (m := z + h) z),
      rankCut (fun i => uniformVector (z + h) (classProfileOrder (binaryHeight z) orders v i))
        (positions v.1).val = ((positions v.1).val : ℝ) / (z + h : ℕ) := by
    intro v
    change rankCut (fun _ : Fin (z + h) => 1 / ((z + h : ℕ) : ℝ)) (positions v.1).val = _
    rw [rankCut_const _ _ (by have := (positions v.1).isLt; omega)]
    ring
  simp_rw [hpoint]
  rw [typeProfile_average]
  have hc : (Fintype.card (heightStabilizer (binaryHeight (m := z + h) z)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  congr 1
  funext t
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end OptimalG
