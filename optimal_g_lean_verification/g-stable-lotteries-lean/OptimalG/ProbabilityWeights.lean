import OptimalG.Finite

/-! # Normalizing finite nonnegative voter-type weights -/

namespace OptimalG
open scoped BigOperators

noncomputable def probabilityNormalize {T : Type*} [Fintype T] (w : T → ℝ) (t : T) : ℝ :=
  w t / ∑ s, w s

theorem probabilityNormalize_average {T : Type*} [Fintype T] (w f : T → ℝ) :
    expectation (probabilityNormalize w) f = expectation w f / ∑ t, w t := by
  simp only [expectation, probabilityNormalize, div_mul_eq_mul_div, Finset.sum_div]

theorem probabilityNormalize_nonneg {T : Type*} [Fintype T] (w : T → ℝ)
    (hw : ∀ t, 0 ≤ w t) : ∀ t, 0 ≤ probabilityNormalize w t := by
  intro t
  exact div_nonneg (hw t) (Finset.sum_nonneg (fun s _ => hw s))

theorem probabilityNormalize_total {T : Type*} [Fintype T] (w : T → ℝ)
    (hpos : 0 < ∑ t, w t) : ∑ t, probabilityNormalize w t = 1 := by
  simp only [probabilityNormalize, ← Finset.sum_div, div_self (ne_of_gt hpos)]

theorem probabilityNormalize_zero {T : Type*} [Fintype T] (w f : T → ℝ)
    (hzero : expectation w f = 0) : expectation (probabilityNormalize w) f = 0 := by
  rw [probabilityNormalize_average, hzero, zero_div]

theorem probabilityNormalize_reference {T : Type*} [Fintype T] (w f : T → ℝ)
    (hpos : 0 < ∑ t, w t) (mean : ℝ) (hcenter : expectation w (fun t => f t - mean) < 0) :
    expectation (probabilityNormalize w) f < mean := by
  rw [probabilityNormalize_average]
  apply (div_lt_iff₀ hpos).mpr
  simp only [expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hcenter
  change (∑ t, w t * f t) < mean * ∑ t, w t
  linarith

theorem probabilityNormalize_excess {T : Type*} [Fintype T] (w N G : T → ℝ)
    (hpos : 0 < ∑ t, w t) (lam : ℝ)
    (hexcess : 0 < expectation w (fun t => N t - lam * G t)) :
    lam * expectation (probabilityNormalize w) G < expectation (probabilityNormalize w) N := by
  rw [probabilityNormalize_average, probabilityNormalize_average, ← mul_div_assoc]
  apply (div_lt_div_iff_of_pos_right hpos).mpr
  simp only [expectation, mul_sub, Finset.sum_sub_distrib, mul_left_comm (w _) lam,
    ← Finset.mul_sum] at hexcess
  exact sub_pos.mp hexcess

end OptimalG
