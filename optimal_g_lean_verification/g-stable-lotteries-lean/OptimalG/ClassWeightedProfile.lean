import OptimalG.TwoClassProfile

/-! # Arbitrary finite mixtures of actual class-symmetrized ranking types -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

noncomputable def typeProfileWeight {T G : Type*} [Fintype G] (w : T → ℝ) (v : T × G) : ℝ :=
  w v.1 / Fintype.card G

theorem typeProfile_average {T G : Type*} [Fintype T] [Fintype G]
    (w : T → ℝ) (f : T × G → ℝ) :
    expectation (typeProfileWeight w) f =
      expectation w (fun t => (∑ sigma : G, f (t, sigma)) / Fintype.card G) := by
  simp only [expectation, typeProfileWeight, Fintype.sum_prod_type, ← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem typeProfileWeight_nonneg {T G : Type*} [Fintype G] (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) :
    ∀ v : T × G, 0 ≤ typeProfileWeight w v := fun v => div_nonneg (hw v.1) (Nat.cast_nonneg _)

theorem typeProfileWeight_total {T G : Type*} [Fintype T] [Fintype G] [Nonempty G]
    (w : T → ℝ) (hwsum : ∑ t, w t = 1) : ∑ v : T × G, typeProfileWeight w v = 1 := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he := typeProfile_average (G := G) w (fun _ => 1)
  simpa only [expectation, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, div_self hc, hwsum] using he

theorem expectation_commute_mul {T C : Type*} [Fintype T] [Fintype C]
    (w : T → ℝ) (D rho : C → ℝ) (f : T → C → ℝ) :
    expectation D (fun x => rho x * expectation w (fun t => f t x)) =
      expectation w (fun t => expectation D (fun x => rho x * f t x)) := by
  calc
    _ = expectation D (fun x => expectation w (fun t => rho x * f t x)) := by
      simp_rw [expectation_smul]
    _ = _ := expectation_commute w D _

def classProfileOrder {T : Type*} {m : ℕ} (rho : Fin m → ℝ)
    (orders : T → Equiv.Perm (Fin m)) (v : T × heightStabilizer rho) : Equiv.Perm (Fin m) :=
  (orders v.1).trans ((heightStabilizer rho).subtype v.2)

theorem classProfile_activation_average {T : Type*} [Fintype T] {m : ℕ}
    (rho : Fin m → ℝ) (orders : T → Equiv.Perm (Fin m)) (w : T → ℝ)
    (g : ℝ → ℝ) (a : Fin m) :
    expectation (typeProfileWeight w) (fun v => orderedActivation g (uniformVector m) (classProfileOrder rho orders v) a) =
      expectation w (fun t => symmetrizedActivation g (uniformVector m) (orders t) (heightStabilizer rho).subtype a) := by
  rw [typeProfile_average]
  rfl

/-- Exact high-class balance in finitely many base rankings is sufficient for
individual stationarity after uniformly permuting labels within both classes. -/
theorem classProfile_stationary {T : Type*} [Fintype T]
    (h z : ℕ) (hh : 0 < h) (hz : 0 < z) [NeZero (h + z)]
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1))
    (orders : T → Equiv.Perm (Fin (h + z))) (w : T → ℝ) (hwsum : ∑ t, w t = 1)
    (hbalance : expectation w (fun t => expectation (uniformVector (h + z))
      (fun x => binaryHeight h x * orderedActivation g (uniformVector (h + z)) (orders t) x)) =
      ((h : ℝ) / (h + z : ℕ)) * (∫ r in (0 : ℝ)..1, g r)) :
    ∀ a, expectation (typeProfileWeight w) (fun v => orderedActivation g (uniformVector (h + z))
      (classProfileOrder (binaryHeight h) orders v) a) = ∫ r in (0 : ℝ)..1, g r := by
  have hm : ((h + z : ℕ) : ℝ) ≠ 0 := by positivity
  have hsum : ∑ x : Fin (h + z), uniformVector (h + z) x = 1 := by
    simp only [uniformVector, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hm
  have hnonneg : ∀ x : Fin (h + z), 0 ≤ uniformVector (h + z) x := fun _ =>
    one_div_nonneg.mpr (Nat.cast_nonneg _)
  intro a
  simp_rw [classProfile_activation_average]
  apply binary_classes_stationary h z hh hz
    (fun x => expectation w (fun t => symmetrizedActivation g (uniformVector (h + z))
      (orders t) (heightStabilizer (binaryHeight h)).subtype x)) _
  · intro x y hxy
    unfold expectation
    apply Finset.sum_congr rfl
    intro t _
    dsimp only
    rw [heightStabilizer_score_eq g _ (orders t) x y hxy]
  · rw [expectation_commute]
    simp_rw [symmetrized_partition g (uniformVector (h + z)) _ _ hg hnonneg hsum]
    exact expectation_const hwsum _
  · rw [expectation_commute_mul]
    simp_rw [heightStabilizer_high_average]
    exact hbalance

end OptimalG
