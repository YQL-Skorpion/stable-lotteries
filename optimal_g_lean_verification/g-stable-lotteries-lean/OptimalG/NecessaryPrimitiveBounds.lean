import OptimalG.NecessaryPositivity
import OptimalG.ThreeClassAlgebra

/-! Integral and determinant bounds for normalized necessary data. -/
namespace OptimalG
open Set MeasureTheory
namespace NormalizedNecessaryTwoClass
variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

theorem primitive_continuous : ContinuousOn (activationPrimitive phi) (Icc 0 1) := by
  have hh := intervalIntegral.continuousOn_primitive_interval'
    (h.continuous.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1))
    (show (0 : ℝ) ∈ Set.uIcc 0 1 by simp)
  change ContinuousOn (fun r => ∫ u in (0 : ℝ)..r, phi u) (Icc 0 1)
  simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hh

theorem primitive_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    activationPrimitive phi b - activationPrimitive phi a = ∫ r in a..b, phi r := by
  have h0 := (h.continuous.mono (Icc_subset_Icc le_rfl hb)).intervalIntegrable_of_Icc (μ := volume) (ha.trans hab)
  have ha' := (h.continuous.mono (Icc_subset_Icc le_rfl (hab.trans hb))).intervalIntegrable_of_Icc (μ := volume) ha
  have hab' := (h.continuous.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc (μ := volume) hab
  have hh := intervalIntegral.integral_add_adjacent_intervals ha' hab'
  unfold activationPrimitive
  linarith

theorem primitive_increment_ceiling {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    activationPrimitive phi b - activationPrimitive phi a ≤ lam * (b - a) - (b ^ 2 - a ^ 2) / 2 := by
  rw [h.primitive_increment ha hab hb]
  have hp := (h.continuous.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi : IntervalIntegrable (fun r : ℝ => r) volume a b := continuous_id.intervalIntegrable a b
  have hl : IntervalIntegrable (fun r : ℝ => lam - r) volume a b := intervalIntegrable_const.sub hi
  have hh := intervalIntegral.integral_mono_on hab hp hl
    (fun r hr => h.ceiling r ⟨ha.trans hr.1, hr.2.trans hb⟩)
  rw [intervalIntegral.integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const,
    integral_id] at hh
  simp only [smul_eq_mul] at hh
  nlinarith

theorem primitive_upper {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    activationPrimitive phi r ≤ lam * r - r ^ 2 / 2 := by
  have hh := h.primitive_increment_ceiling (a := 0) le_rfl hr.1 hr.2
  simpa [activationPrimitive] using hh

theorem primitive_reverse_lower {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    lam * r - r ^ 2 / 2 - (lam - 1 / 2) ≤ activationPrimitive phi r := by
  have hh := h.primitive_increment_ceiling hr.1 hr.2 le_rfl
  rw [h.integral_zero] at hh
  nlinarith

theorem third_class_K_pos {p z : ℝ} (hp : 0 < p) (hpL : p < lam)
    (hz : lam + p / 2 < z) (hz1 : z ≤ 1) :
    0 < activationPrimitive phi (z - p) - activationPrimitive phi z := by
  have hzp : 0 ≤ z - p := by linarith
  have hh := h.primitive_increment_ceiling hzp (show z - p ≤ z by linarith) hz1
  have hp' := mul_pos hp (show 0 < z - lam - p / 2 by linarith)
  nlinarith

theorem third_class_determinant_pos (hL0 : 0 < lam) (hL1 : lam < 1)
    {p x y : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x < lam) (hy : y < lam) :
    0 < (2 * lam - x) * activationPrimitive phi p -
      (p + y - lam) * activationPrimitive phi (1 - p) := by
  apply three_class_determinant_positive hL0 hp.1 hx hy
    (h.primitive_pos hL0 hL1 p hp) (h.primitive_pos hL0 hL1 (1 - p) ⟨by linarith [hp.2], by linarith [hp.1]⟩)
  have hh := h.two_class_all hL0 hL1 p 0 hp le_rfl hp.1.le hL0.le
  simpa [activationPrimitive] using hh

/-- Equation (3.7), with both primitive and determinant positivity proved from
the necessary data. The remaining test premise is supplied by actual Election 3. -/
theorem third_class_of_weight_test (hL0 : 0 < lam) (hL1 : lam < 1)
    {p x y z : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x < lam) (hpy : p ≤ y) (hy : y < lam)
    (hz : lam + p / 2 < z) (hz1 : z ≤ 1)
    (hX : 0 < (z - lam) * activationPrimitive phi p +
      (p + y - lam) * (activationPrimitive phi (z - p) - activationPrimitive phi z))
    (htest : ThreeClassWeightTest (activationPrimitive phi p) (activationPrimitive phi (1 - p))
      (activationPrimitive phi (z - p) - activationPrimitive phi z)
      (phi x) (phi y) (phi z) (2 * lam - x) (z - lam) (p + y - lam)) :
    ((z - lam) * activationPrimitive phi p +
        (p + y - lam) * (activationPrimitive phi (z - p) - activationPrimitive phi z)) * phi x +
      ((z - lam) * activationPrimitive phi (1 - p) +
        (2 * lam - x) * (activationPrimitive phi (z - p) - activationPrimitive phi z)) * phi y +
      ((2 * lam - x) * activationPrimitive phi p -
        (p + y - lam) * activationPrimitive phi (1 - p)) * phi z ≤ 0 :=
  three_class_minors_nonpos (h.primitive_pos hL0 hL1 p hp)
    (h.primitive_pos hL0 hL1 (1 - p) ⟨by linarith [hp.2], by linarith [hp.1]⟩)
    (h.third_class_K_pos hp.1 (hpy.trans_lt hy) hz hz1)
    (h.third_class_determinant_pos hL0 hL1 hp hx hy) hX htest

end NormalizedNecessaryTwoClass
end OptimalG
