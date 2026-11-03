import OptimalG.ClassSymmetry
import OptimalG.UniformScoreBlocks

/-! # Actual two-class finite weighted elections -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

noncomputable def twoTypeWeight {G : Type*} [Fintype G] (theta : ℝ) (v : Fin 2 × G) : ℝ :=
  (if v.1 = 0 then theta else 1 - theta) / Fintype.card G

theorem twoType_average {G : Type*} [Fintype G] (theta : ℝ) (f : Fin 2 × G → ℝ) :
    expectation (twoTypeWeight theta) f =
      theta * ((∑ sigma : G, f (0, sigma)) / Fintype.card G) +
      (1 - theta) * ((∑ sigma : G, f (1, sigma)) / Fintype.card G) := by
  simp [expectation, twoTypeWeight, Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.mul_sum]
  ring

theorem twoTypeWeight_nonneg {G : Type*} [Fintype G] (theta : ℝ) (htheta : theta ∈ Icc 0 1) :
    ∀ v : Fin 2 × G, 0 ≤ twoTypeWeight theta v := by
  intro v
  unfold twoTypeWeight
  apply div_nonneg _ (Nat.cast_nonneg _)
  split_ifs
  · exact htheta.1
  · linarith [htheta.2]

theorem twoTypeWeight_total {G : Type*} [Fintype G] [Nonempty G] (theta : ℝ) :
    ∑ v : Fin 2 × G, twoTypeWeight theta v = 1 := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs := twoType_average (G := G) theta (fun _ => 1)
  simpa only [expectation, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, div_self hc, sub_add_cancel, add_sub_cancel] using hs

/-- The primitive of the unscaled centered activation τ-g. -/
noncomputable def centeredPrimitive (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * activationPrimitive g 1 - activationPrimitive g r

/-- The two actual finite rank-block profiles, uniformly symmetrized inside
height classes, have the stated exact stationarity and metric quantities. -/
theorem exists_two_class_profile (g : ℝ → ℝ) (hg : Continuous g)
    (h z k : ℕ) (hh : 0 < h) (hz : 0 < z) (hk : k < h) [NeZero (h + z)]
    (theta : ℝ) (htheta : theta ∈ Icc 0 1)
    (hbalance : theta *
        (centeredPrimitive g (((k + z : ℕ) : ℝ) / (h + z : ℕ)) - centeredPrimitive g ((k : ℝ) / (h + z : ℕ))) -
      (1 - theta) * centeredPrimitive g ((h : ℝ) / (h + z : ℕ)) = 0) :
    ∃ (orders : (Fin 2 × heightStabilizer (binaryHeight (m := h + z) h)) → Equiv.Perm (Fin (h + z))),
      (∀ x, expectation (twoTypeWeight theta) (fun v =>
        orderedActivation g (uniformVector (h + z)) (orders v) x) = activationPrimitive g 1) ∧
      expectation (twoTypeWeight theta) (fun v =>
        expectation (uniformVector (h + z))
          (runningMin (fun x => ((orders v).symm x).val) (binaryHeight h))) =
          theta * ((k : ℝ) / (h + z : ℕ)) + (1 - theta) * ((h : ℝ) / (h + z : ℕ)) ∧
      expectation (twoTypeWeight theta) (fun v =>
        maximumGap (fun x => ((orders v).symm x).val) (binaryHeight h)) = theta := by
  classical
  let m := h + z
  let G := heightStabilizer (binaryHeight (m := m) h)
  let u := uniformVector m
  let mean := activationPrimitive g 1
  have hm : (m : ℝ) ≠ 0 := by dsimp [m]; positivity
  have hsum : ∑ x : Fin m, u x = 1 := by
    simp only [u, uniformVector, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hm
  have hnonneg : ∀ x : Fin m, 0 ≤ u x := fun _ => one_div_nonneg.mpr (Nat.cast_nonneg _)
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨o1, ho1⟩ := exists_binary_block_order h z k hk.le
  obtain ⟨o2, ho2⟩ := exists_binary_block_order h z h le_rfl
  let orders := fun v : Fin 2 × G =>
    (if v.1 = 0 then o1 else o2).trans ((heightStabilizer (binaryHeight h)).subtype v.2)
  have hshape1 (sigma : G) (i : Fin m) :
      binaryHeight h ((orders (0, sigma)) i) = if i.val < k ∨ k + z ≤ i.val then 1 else 0 := by
    change binaryHeight h (sigma.val (o1 i)) = _
    rw [sigma.property, ho1]
  have hshape2 (sigma : G) (i : Fin m) :
      binaryHeight h ((orders (1, sigma)) i) = if i.val < h ∨ h + z ≤ i.val then 1 else 0 := by
    change binaryHeight h (sigma.val (o2 i)) = _
    rw [sigma.property, ho2]
  let F1 := symmetrizedActivation g u o1 (heightStabilizer (binaryHeight h)).subtype
  let F2 := symmetrizedActivation g u o2 (heightStabilizer (binaryHeight h)).subtype
  have haverage (x : Fin m) :
      expectation (twoTypeWeight theta) (fun v => orderedActivation g u (orders v) x) =
        theta * F1 x + (1 - theta) * F2 x := by
    rw [twoType_average]
    rfl
  have htotal1 : expectation u F1 = mean :=
    symmetrized_partition g u o1 _ hg.continuousOn hnonneg hsum
  have htotal2 : expectation u F2 = mean :=
    symmetrized_partition g u o2 _ hg.continuousOn hnonneg hsum
  have hhigh1 : expectation u (fun x => binaryHeight h x * F1 x) =
      mean - (activationPrimitive g (((k + z : ℕ) : ℝ) / m) - activationPrimitive g ((k : ℝ) / m)) := by
    rw [heightStabilizer_high_average]
    exact uniform_high_class_activation g hg o1 (binaryHeight h) k (k + z) (by omega) (by omega) ho1
  have hhigh2 : expectation u (fun x => binaryHeight h x * F2 x) = activationPrimitive g ((h : ℝ) / m) := by
    rw [heightStabilizer_high_average]
    have he := uniform_high_class_activation g hg o2 (binaryHeight h) h (h + z)
      (by omega) le_rfl ho2
    have hm' : ((h + z : ℕ) : ℝ) ≠ 0 := hm
    simpa only [div_self hm', sub_sub_cancel] using he
  refine ⟨orders, ?_, ?_, ?_⟩
  · intro a
    rw [haverage]
    apply binary_classes_stationary h z hh hz (fun x => theta * F1 x + (1 - theta) * F2 x) mean
    · intro x y hxy
      dsimp [F1, F2, u]
      rw [heightStabilizer_score_eq g _ o1 x y hxy, heightStabilizer_score_eq g _ o2 x y hxy]
    · rw [expectation_add, expectation_smul, expectation_smul, htotal1, htotal2]
      ring
    · have he : expectation u (fun x => binaryHeight h x * (theta * F1 x + (1 - theta) * F2 x)) =
        theta * expectation u (fun x => binaryHeight h x * F1 x) +
          (1 - theta) * expectation u (fun x => binaryHeight h x * F2 x) := by
        simp only [expectation, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
      rw [he, hhigh1, hhigh2]
      dsimp [centeredPrimitive] at hbalance
      have hm1 : ((h : ℝ) + (z : ℝ)) / (m : ℝ) = 1 := by rw [← Nat.cast_add]; exact div_self hm
      have hcast : ((k + z : ℕ) : ℝ) = (k : ℝ) + z := by push_cast; rfl
      rw [hcast] at hbalance
      dsimp [m, mean] at *
      push_cast at *
      field_simp at hm1
      field_simp
      field_simp at hbalance
      nlinarith
  · rw [twoType_average]
    have hcost1 (sigma : G) := (binary_block_geometry h z k hz hk.le (orders (0, sigma)) (hshape1 sigma)).1
    have hcost2 (sigma : G) := (binary_block_geometry h z h hz le_rfl (orders (1, sigma)) (hshape2 sigma)).1
    simp_rw [hcost1, hcost2]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc' : (Fintype.card (heightStabilizer (binaryHeight (m := h + z) h)) : ℝ) ≠ 0 := hc
    field_simp
  · rw [twoType_average]
    have hgap1 (sigma : G) := (binary_block_geometry h z k hz hk.le (orders (0, sigma)) (hshape1 sigma)).2
    have hgap2 (sigma : G) := (binary_block_geometry h z h hz le_rfl (orders (1, sigma)) (hshape2 sigma)).2
    simp_rw [hgap1, hgap2]
    simp [hk, hc]

end OptimalG
