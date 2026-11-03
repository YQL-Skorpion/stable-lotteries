import OptimalG.UniversalSlackBounds
import OptimalG.PhaseControlBounds

/-! Initial scalar boxes for the actual necessary primitive, prior to relocation. -/
namespace OptimalG
open Set

noncomputable def universalLowCurve (p : ℝ) : ℝ :=
  0.562325 * p - p ^ 2 / 2 - 0.0266503148804352
noncomputable def universalComplementCurve (p : ℝ) : ℝ :=
  0.562330 * (1 - p) - (1 - p) ^ 2 / 2 - 0.02196

/-- A four-term Bernstein identity proves the calibrated binary margin. -/
theorem universal_binary_curve_lower {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    (0.01448 : ℝ) ≤ 0.562325 * universalLowCurve p - p * universalComplementCurve p := by
  apply sub_nonneg.mp
  have heq : 0.562325 * universalLowCurve p - p * universalComplementCurve p - 0.01448 =
      (929367906683311 / 519921875000000 : ℝ) * (0.36 - p)^3 +
      (12900926003246607 / 2079687500000000 : ℝ) * (p - 0.25) * (0.36 - p)^2 +
      (4074426961584241 / 1039843750000000 : ℝ) * (p - 0.25)^2 * (0.36 - p) +
      (5243296655119 / 2079687500000000 : ℝ) * (p - 0.25)^3 := by
    unfold universalLowCurve universalComplementCurve
    ring
  rw [heq]
  have ha : 0 ≤ p - 0.25 := by linarith [hp.1]
  have hb : 0 ≤ 0.36 - p := by linarith [hp.2]
  positivity

/-- A second exact Bernstein identity gives a stronger initial determinant box. -/
theorem universal_det_curve_lower {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    (0.0535 : ℝ) ≤ (2 * 0.562325 - 0.38) * universalLowCurve p -
      (p + 0.38 - 0.562325) * universalComplementCurve p := by
  apply sub_nonneg.mp
  have heq : (2 * 0.562325 - 0.38) * universalLowCurve p -
      (p + 0.38 - 0.562325) * universalComplementCurve p - 0.0535 =
      (36197675221819 / 1039843750000000 : ℝ) * (0.36 - p)^3 +
      (8817047588165457 / 1039843750000000 : ℝ) * (p - 0.25) * (0.36 - p)^2 +
      (12551669533477957 / 1039843750000000 : ℝ) * (p - 0.25)^2 * (0.36 - p) +
      (4290741495534319 / 1039843750000000 : ℝ) * (p - 0.25)^3 := by
    unfold universalLowCurve universalComplementCurve
    ring
  rw [heq]
  have ha : 0 ≤ p - 0.25 := by linarith [hp.1]
  have hb : 0 ≤ 0.36 - p := by linarith [hp.2]
  positivity

namespace NormalizedNecessaryTwoClass
variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

theorem primitive_low_curve (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    universalLowCurve p ≤ activationPrimitive phi p := by
  have hh := h.primitive_lower_before_half hL hLP (r := p) ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hprod := mul_nonneg (show 0 ≤ lam - 0.562325 by linarith [hL.1]) (show 0 ≤ p by linarith [hp.1])
  unfold universalLowCurve linePrimitive universalScalarUpper at *
  nlinarith [hL.2]

theorem primitive_complement_curve (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    activationPrimitive phi (1 - p) ≤ universalComplementCurve p := by
  have hh := h.primitive_upper_after_half hL hLP (r := 1 - p) ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hprod := mul_nonneg (show 0 ≤ 0.562330 - lam by linarith [hL.2])
    (show 0 ≤ 1 - p by linarith [hp.2])
  unfold universalComplementCurve linePrimitive at *
  nlinarith

theorem initial_binary_margin (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    (0.01446 : ℝ) < lam * activationPrimitive phi p - p * activationPrimitive phi (1 - p) := by
  have hR := h.primitive_low_rank_lower hL hLP hp
  have hlow := mul_le_mul_of_nonneg_left (h.primitive_low_curve hL hLP hp)
    (by norm_num : (0 : ℝ) ≤ 0.562325)
  have hscale := mul_le_mul_of_nonneg_right hL.1 (show 0 ≤ activationPrimitive phi p by linarith)
  have hupper := mul_le_mul_of_nonneg_left (h.primitive_complement_curve hL hLP hp)
    (show 0 ≤ p by linarith [hp.1])
  have hnum := universal_binary_curve_lower hp
  nlinarith only [hlow, hscale, hupper, hnum]

theorem initial_determinant_margin (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p x y : ℝ}
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hx : x ∈ Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Icc (0.285 : ℝ) 0.38) :
    (0.0535 : ℝ) ≤ (2 * lam - x) * activationPrimitive phi p -
      (p + y - lam) * activationPrimitive phi (1 - p) := by
  have hR := h.primitive_low_rank_lower hL hLP hp
  have hP := h.primitive_pos (by linarith [hL.1]) (by linarith [hL.2]) (1 - p)
    ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hlow := mul_le_mul_of_nonneg_left (h.primitive_low_curve hL hLP hp)
    (by norm_num : (0 : ℝ) ≤ 2 * 0.562325 - 0.38)
  have hscale := mul_le_mul_of_nonneg_right
    (show 2 * 0.562325 - 0.38 ≤ 2 * lam - x by linarith [hL.1, hx.2])
    (show 0 ≤ activationPrimitive phi p by linarith)
  have hupper := mul_le_mul (show p + y - lam ≤ p + 0.38 - 0.562325 by linarith [hy.2, hL.1])
    (h.primitive_complement_curve hL hLP hp) hP.le (show 0 ≤ p + 0.38 - 0.562325 by linarith [hp.1])
  have hnum := universal_det_curve_lower hp
  nlinarith only [hlow, hscale, hupper, hnum]

theorem available_low_slack (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    (0.014975 : ℝ) < cumulativeSlack lam phi 0.245 := by
  have hL0 : 0 < lam := by linarith [hL.1]
  have hL1 : lam < 1 := by linarith [hL.2]
  have hP := h.primitive_pos hL0 hL1 0.755 (by norm_num)
  have hPup := h.primitive_upper_after_half hL hLP (r := 0.755) (by norm_num)
  have hPnum : activationPrimitive phi 0.755 < (0.1176 : ℝ) := by
    unfold linePrimitive at hPup
    nlinarith [hL.2]
  have hbinary := h.two_class_all hL0 hL1 0.755 0 (by norm_num) le_rfl (by norm_num) hL0.le
  norm_num [activationPrimitive] at hbinary
  have hbinary' : (0.755 : ℝ) * activationPrimitive phi 0.245 ≤ lam * activationPrimitive phi 0.755 := by
    convert! hbinary using 1 <;> norm_num [activationPrimitive]
  have hprod := mul_le_mul hL.2 hPnum.le hP.le (by norm_num : (0 : ℝ) ≤ 0.562330)
  unfold cumulativeSlack linePrimitive
  nlinarith [hL.1]

theorem initial_gap_bounds (hL : Certificates.Compact.LambdaRange lam)
    {p z : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hz : z ∈ Icc (0.775 : ℝ) 0.875) :
    0 < activationPrimitive phi (z - p) - activationPrimitive phi z ∧
      activationPrimitive phi (z - p) - activationPrimitive phi z < (0.159 : ℝ) := by
  have hL0 : 0 < lam := by linarith [hL.1]
  have hL1 : lam < 1 := by linarith [hL.2]
  refine ⟨h.third_class_K_pos (by linarith [hp.1]) (by linarith [hp.2, hL.1])
    (by linarith [hz.1, hp.2, hL.2]) (by linarith [hz.2]), ?_⟩
  have hJ := h.primitive_upper (r := z - p) ⟨by linarith [hz.1, hp.2], by linarith [hz.2, hp.1]⟩
  have hzpos := h.primitive_pos hL0 hL1 z ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hLs := mul_nonneg (show 0 ≤ 0.562330 - lam by linarith [hL.2])
    (show 0 ≤ 0.562330 + lam by linarith [hL.1])
  nlinarith [sq_nonneg (z - p - lam)]

theorem initial_control_coefficients_positive (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p x y z : ℝ}
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hx : x ∈ Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Icc (0.285 : ℝ) 0.38) (hz : z ∈ Icc (0.775 : ℝ) 0.875) :
    0 < (z - lam) * activationPrimitive phi p +
      (p + y - lam) * (activationPrimitive phi (z - p) - activationPrimitive phi z) ∧
    0 < (z - lam) * activationPrimitive phi (1 - p) +
      (2 * lam - x) * (activationPrimitive phi (z - p) - activationPrimitive phi z) := by
  have hR := h.primitive_low_rank_lower hL hLP hp
  have hP := h.primitive_pos (by linarith [hL.1]) (by linarith [hL.2]) (1 - p)
    ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hK := h.initial_gap_bounds hL hp hz
  have hU : 0 < z - lam := by linarith [hz.1, hL.2]
  have hH : 0 < 2 * lam - x := by linarith [hL.1, hx.2]
  constructor
  · have hUR := mul_le_mul (show (0.21267 : ℝ) ≤ z - lam by linarith [hz.1, hL.2])
      hR.le (by norm_num : (0 : ℝ) ≤ 0.0826) hU.le
    have hk := mul_le_mul_of_nonneg_right
      (show (-0.02733 : ℝ) ≤ p + y - lam by linarith [hp.1, hy.1, hL.2]) hK.1.le
    have hkb := mul_le_mul_of_nonpos_left hK.2.le (by norm_num : (-0.02733 : ℝ) ≤ 0)
    nlinarith only [hUR, hk, hkb]
  · exact add_pos (mul_pos hU hP) (mul_pos hH hK.1)

end NormalizedNecessaryTwoClass
end OptimalG
