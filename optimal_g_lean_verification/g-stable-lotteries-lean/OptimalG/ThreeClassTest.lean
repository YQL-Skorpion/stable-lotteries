import OptimalG.ThreeClassLimit
import OptimalG.ThreeClassAlgebra

/-! # The Election 3 weight test follows from actual universal distortion -/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators

theorem probabilityNormalize_reference_le {T : Type*} [Fintype T] (w f : T → ℝ)
    (hpos : 0 < ∑ t, w t) (mean : ℝ) (hcenter : expectation w (fun t => f t - mean) ≤ 0) :
    expectation (probabilityNormalize w) f ≤ mean := by
  rw [probabilityNormalize_average]
  apply (div_le_iff₀ hpos).mpr
  simp only [expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hcenter
  change (∑ t, w t * f t) ≤ mean * ∑ t, w t
  linarith

/-- No hidden real-voter realization hypothesis occurs in this test. A strict
violation produces a finite equal-voter election by `real_three_class_strict_witness`. -/
theorem three_class_weight_test_of_universalBound (g : ℝ → ℝ) (hg : Continuous g)
    (lam p x y z : ℝ) (hlam : 0 ≤ lam) (hbound : UniversalBound g (1 + 2 * lam))
    (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) (hxp : x < 1 - p)
    (hpy : p ≤ y) (hy1 : y < 1) (hpz : p < z) (hz1 : z ≤ 1)
    (hR : 0 < centeredPrimitive g p) (hP : 0 < centeredPrimitive g (1 - p)) :
    ThreeClassWeightTest (centeredPrimitive g p) (centeredPrimitive g (1 - p))
      (centeredPrimitive g (z - p) - centeredPrimitive g z)
      (activationPrimitive g 1 - g x) (activationPrimitive g 1 - g y) (activationPrimitive g 1 - g z)
      (2 * lam - x) (z - lam) (p + y - lam) := by
  intro w1 w2 w3 hw1 hw2 hw3 hbalance hreference
  by_contra! hexcess
  let W : Fin 3 → ℝ := ![w1, w2, w3]
  have hW : ∀ t, 0 ≤ W t := by intro t; fin_cases t <;> assumption
  have hsum : ∑ t, W t = w1 + w2 + w3 := by simp [W, Fin.sum_univ_three]
  have hpos : 0 < ∑ t, W t := by
    rw [hsum]
    by_contra! hn
    have h1 : w1 = 0 := by linarith
    have h2 : w2 = 0 := by linarith
    have h3 : w3 = 0 := by linarith
    simp only [h1, h2, h3, mul_zero, zero_add, add_zero, lt_self_iff_false] at hexcess
  have hbalW : expectation W ![centeredPrimitive g (1 - p),
      centeredPrimitive g (z - p) - centeredPrimitive g z, -centeredPrimitive g p] = 0 := by
    simp only [expectation, Fin.sum_univ_three]
    change _
    dsimp [W]
    nlinarith only [hbalance]
  have hrefW : expectation W (fun t => ![g x, g z, g y] t - activationPrimitive g 1) ≤ 0 := by
    simp only [expectation, Fin.sum_univ_three]
    change _
    dsimp [W]
    nlinarith only [hreference]
  have hexcW : 0 < expectation W (fun t => ![x, z, p + y] t - lam * ![2, 1, 1] t) := by
    simp only [expectation, Fin.sum_univ_three]
    change _
    dsimp [W]
    nlinarith only [hexcess]
  have hexc : 0 < expectation (probabilityNormalize W) (fun t => ![x, z, p + y] t - lam * ![2, 1, 1] t) := by
    rw [probabilityNormalize_average]
    exact div_pos hexcW hpos
  have hend := endpoint_above_mean_of_universalBound g lam hlam hbound
  obtain ⟨r, hr, hrbelow⟩ := exists_rank_below_mean g hg.continuousOn hend
  exact witnessAbove_not_universalBound g _
    (real_three_class_strict_witness g hg lam p x y z hlam hp hx hxp hpy hy1 hpz hz1 r hr hrbelow hend
      hR hP (probabilityNormalize W) (probabilityNormalize_nonneg W hW) (probabilityNormalize_total W hpos)
      (probabilityNormalize_zero W _ hbalW) (probabilityNormalize_reference_le W _ hpos _ hrefW) hexc) hbound

/-- Positive rescaling of all primitive and reference scores preserves the
test because its balance and reference constraints are homogeneous. -/
theorem ThreeClassWeightTest.scale {R P K A B C h U k : ℝ}
    (htest : ThreeClassWeightTest R P K A B C h U k) (c : ℝ) (hc : 0 < c) :
    ThreeClassWeightTest (c * R) (c * P) (c * K) (c * A) (c * B) (c * C) h U k := by
  intro w1 w2 w3 hw1 hw2 hw3 hbalance hreference
  have hbal : P * w1 + K * w2 - R * w3 = 0 := by
    have he : c * (P * w1 + K * w2 - R * w3) = 0 := by nlinarith only [hbalance]
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hc)
  have href : 0 ≤ A * w1 + C * w2 + B * w3 := by
    have he : 0 ≤ c * (A * w1 + C * w2 + B * w3) := by nlinarith only [hreference]
    exact nonneg_of_mul_nonneg_right he hc
  exact htest w1 w2 w3 hw1 hw2 hw3 hbal href

end OptimalG
