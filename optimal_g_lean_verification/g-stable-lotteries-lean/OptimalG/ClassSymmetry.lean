import OptimalG.BinaryRanking

/-! # Finite symmetrization inside height classes -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

def heightStabilizer {C : Type*} (rho : C → ℝ) : Subgroup (Equiv.Perm C) where
  carrier := {sigma | ∀ x, rho (sigma x) = rho x}
  one_mem' := fun _ => rfl
  mul_mem' ha hb x := by rw [Equiv.Perm.mul_apply, ha, hb]
  inv_mem' := by
    intro sigma ha x
    exact (ha (sigma.symm x)).symm.trans (congrArg rho (sigma.apply_symm_apply x))

noncomputable instance heightStabilizer_fintype {C : Type*} [Fintype C] (rho : C → ℝ) :
    Fintype (heightStabilizer rho) := Fintype.ofFinite _

theorem heightStabilizer_transitive {C : Type*} [DecidableEq C]
    (rho : C → ℝ) (a b : C) (hab : rho a = rho b) :
    ∃ sigma : heightStabilizer rho, (heightStabilizer rho).subtype sigma a = b := by
  refine ⟨⟨Equiv.swap a b, ?_⟩, by simp⟩
  intro x
  by_cases hxa : x = a
  · subst x; simpa using hab.symm
  by_cases hxb : x = b
  · subst x; simpa using hab
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem heightStabilizer_score_eq {m : ℕ} (g : ℝ → ℝ) (rho : Fin m → ℝ)
    (order : Equiv.Perm (Fin m)) (a b : Fin m) (hab : rho a = rho b) :
    symmetrizedActivation g (uniformVector m) order (heightStabilizer rho).subtype a =
      symmetrizedActivation g (uniformVector m) order (heightStabilizer rho).subtype b := by
  obtain ⟨sigma, hsigma⟩ := heightStabilizer_transitive rho a b hab
  have hi := symmetrizedActivation_invariant g (uniformVector m) order (heightStabilizer rho).subtype
    (fun _ _ => rfl) sigma a
  rw [hsigma] at hi
  exact hi.symm

theorem heightStabilizer_high_average {m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (rho : Fin m → ℝ) (order : Equiv.Perm (Fin m)) :
    expectation (uniformVector m) (fun x => rho x *
      symmetrizedActivation g (uniformVector m) order (heightStabilizer rho).subtype x) =
      expectation (uniformVector m) (fun x => rho x * orderedActivation g (uniformVector m) order x) := by
  classical
  let G := heightStabilizer rho
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsingle (sigma : G) : expectation (uniformVector m) (fun x => rho x *
      orderedActivation g (uniformVector m) (order.trans ((heightStabilizer rho).subtype sigma)) x) =
      expectation (uniformVector m) (fun x => rho x * orderedActivation g (uniformVector m) order x) := by
    unfold expectation
    rw [← Equiv.sum_comp ((heightStabilizer rho).subtype sigma)]
    apply Finset.sum_congr rfl
    intro x _
    dsimp only
    rw [orderedActivation_relabel g (uniformVector m) order _ (fun _ => rfl), Equiv.symm_apply_apply]
    change (1 / (m : ℝ)) * (rho (sigma.val x) * _) = (1 / (m : ℝ)) * (rho x * _)
    rw [sigma.property]
  let wg := fun _ : G => (1 : ℝ) / Fintype.card G
  have hwg : ∑ sigma : G, wg sigma = 1 := by simp [wg, hc]
  calc
    _ = expectation (uniformVector m) (fun x => expectation wg (fun sigma => rho x *
        orderedActivation g (uniformVector m) (order.trans ((heightStabilizer rho).subtype sigma)) x)) := by
      congr 1
      funext x
      rw [expectation_smul]
      rw [symmetrizedActivation_eq_expectation]
    _ = expectation wg (fun sigma => expectation (uniformVector m) (fun x => rho x *
        orderedActivation g (uniformVector m) (order.trans ((heightStabilizer rho).subtype sigma)) x)) := by
      rw [expectation_commute]
    _ = _ := by
      simp_rw [hsingle]
      exact expectation_const hwg _

theorem binaryHeight_mass (h z : ℕ) [NeZero (h + z)] :
    expectation (uniformVector (h + z)) (binaryHeight h) = (h : ℝ) / (h + z : ℕ) := by
  unfold expectation binaryHeight uniformVector
  have heq : ∀ i : Fin (h + z), (1 / ((h + z : ℕ) : ℝ)) * (if i.val < h then 1 else 0) =
      if i.val < h then (1 : ℝ) / (h + z : ℕ) else 0 := by intro i; split_ifs <;> ring
  simp_rw [heq]
  change rankCut (fun _ : Fin (h + z) => 1 / ((h + z : ℕ) : ℝ)) h = _
  rw [rankCut_const _ _ (by omega)]
  ring

/-- The two class balances and exact rank-partition identity imply every
individual candidate's stationarity after finite class symmetrization. -/
theorem binary_classes_stationary (h z : ℕ) (hh : 0 < h) (hz : 0 < z)
    [NeZero (h + z)] (F : Fin (h + z) → ℝ) (mean : ℝ)
    (hinvariant : ∀ a b, binaryHeight h a = binaryHeight h b → F a = F b)
    (htotal : expectation (uniformVector (h + z)) F = mean)
    (hhigh : expectation (uniformVector (h + z)) (fun x => binaryHeight h x * F x) =
      ((h : ℝ) / (h + z : ℕ)) * mean) : ∀ a, F a = mean := by
  let p : ℝ := (h : ℝ) / (h + z : ℕ)
  have hp : 0 < p := div_pos (by exact_mod_cast hh) (by positivity)
  have hp1 : p < 1 := by apply (div_lt_one (by positivity : (0 : ℝ) < (h + z : ℕ))).mpr; exact_mod_cast (by omega : h < h + z)
  have hm : ((h + z : ℕ) : ℝ) ≠ 0 := by positivity
  have hsum : ∑ x : Fin (h + z), uniformVector (h + z) x = 1 := by
    simp only [uniformVector, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hm
  intro a
  by_cases ha : a.val < h
  · have hterm : ∀ x, binaryHeight h x * F x = binaryHeight h x * F a := by
      intro x
      by_cases hx : x.val < h
      · rw [hinvariant x a (by simp [binaryHeight, hx, ha])]
      · simp [binaryHeight, hx]
    simp_rw [hterm] at hhigh
    have heq : p * F a = p * mean := by
      simp only [expectation, ← mul_assoc, ← Finset.sum_mul] at hhigh
      change expectation (uniformVector (h + z)) (binaryHeight h) * F a = p * mean at hhigh
      rw [binaryHeight_mass] at hhigh
      exact hhigh
    exact mul_left_cancel₀ (ne_of_gt hp) heq
  · have hterm : ∀ x, F x - binaryHeight h x * F x = (1 - binaryHeight h x) * F a := by
      intro x
      by_cases hx : x.val < h
      · simp [binaryHeight, hx]
      · rw [hinvariant x a (by simp [binaryHeight, hx, ha])]
        ring
    have heq : expectation (uniformVector (h + z)) (fun x => F x - binaryHeight h x * F x) =
        (1 - p) * F a := by
      simp_rw [hterm]
      simp only [expectation, ← mul_assoc, ← Finset.sum_mul, mul_sub, mul_one,
        Finset.sum_sub_distrib, hsum]
      change (1 - expectation (uniformVector (h + z)) (binaryHeight h)) * F a = _
      rw [binaryHeight_mass]
    have heq2 : (1 - p) * F a = (1 - p) * mean := by
      rw [← heq]
      simp only [expectation, mul_sub, Finset.sum_sub_distrib] at *
      rw [htotal, hhigh]
      ring
    exact mul_left_cancel₀ (ne_of_gt (sub_pos.mpr hp1)) heq2

end OptimalG
