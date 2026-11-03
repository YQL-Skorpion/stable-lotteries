import OptimalG.TwoClassLimit

/-! # Normalized necessary data derived from actual finite-election bounds -/

namespace OptimalG
open Set MeasureTheory

theorem scaled_centered_primitive (g : ℝ → ℝ) (hg : Continuous g) (c r : ℝ) :
    activationPrimitive (fun x => c * (activationPrimitive g 1 - g x)) r =
      c * centeredPrimitive g r := by
  unfold activationPrimitive
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const (hg.intervalIntegrable 0 r),
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, centeredPrimitive, activationPrimitive]

/-- These are the necessary statements already obtained from actual equal-voter
elections. Positivity of the primitive at every interior rank is deliberately
not assumed here; the two-class test is what permits that further deduction. -/
structure NormalizedNecessaryTwoClass (lam : ℝ) (phi : ℝ → ℝ) : Prop where
  continuous : ContinuousOn phi (Icc 0 1)
  integral_zero : activationPrimitive phi 1 = 0
  endpoint : phi 1 ≤ -1
  ceiling : ∀ r ∈ Icc (0 : ℝ) 1, phi r ≤ lam - r
  two_class : ∀ p q : ℝ, p ∈ Ioo 0 1 → 0 ≤ q → q ≤ p → q ≤ lam →
    0 < activationPrimitive phi p →
    p * (activationPrimitive phi (1 - p + q) - activationPrimitive phi q) ≤
      (lam - q) * activationPrimitive phi p

/-- Every continuous activation with a finite universal distortion bound has
normalized necessary data, with the primitive literally its interval integral.
The relation to the original activation holds at every actual rank. -/
theorem exists_normalized_necessary_twoClass (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1)) (lam : ℝ) (hlam : 0 ≤ lam)
    (hbound : UniversalBound g (1 + 2 * lam)) :
    ∃ (phi : ℝ → ℝ) (c : ℝ), 0 < c ∧
      (∀ r ∈ Icc (0 : ℝ) 1, phi r = c * (activationPrimitive g 1 - g r)) ∧
      NormalizedNecessaryTwoClass lam phi := by
  let gc := clippedActivation g
  have hgc : Continuous gc := clippedActivation_continuous g hg
  have hbc : UniversalBound gc (1 + 2 * lam) := (universalBound_clipped_iff g _).mpr hbound
  obtain ⟨c, hc, hcont, hzero, hend, hcap⟩ := exists_centered_activation gc lam hlam hgc.continuousOn hbc
  let phi := fun r => c * (activationPrimitive gc 1 - gc r)
  refine ⟨phi, c, hc, ?_, ⟨hcont, hzero, hend, hcap, ?_⟩⟩
  · intro r hr
    dsimp [phi, gc]
    rw [clippedActivation_eq g r hr]
    congr 2
    exact clippedActivation_mean g
  · intro p q hp hq hqp hqlam hR
    have hJ : ∀ r, activationPrimitive phi r = c * centeredPrimitive gc r :=
      scaled_centered_primitive gc hgc c
    have hRp : 0 < centeredPrimitive gc p := by
      rw [hJ] at hR
      by_contra! hn
      have := mul_nonpos_of_nonneg_of_nonpos hc.le hn
      linarith
    have htest := real_two_class_necessary gc hgc lam hlam hbc p q hp hq hqp hqlam hRp
    have hscaled := mul_le_mul_of_nonneg_left htest hc.le
    simp_rw [hJ]
    nlinarith only [hscaled]

end OptimalG
