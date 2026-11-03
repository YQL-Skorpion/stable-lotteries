import OptimalG.UniversalControlBoxes

/-! Uniform interpolation boxes for bounded low and middle slack removal.
The common gain eta is included in both R and P; only the extra middle gain
can worsen the binary and determinant margins. -/
namespace OptimalG
open Set

namespace NormalizedNecessaryTwoClass
variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

theorem initial_complement_sharp_upper (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    activationPrimitive phi (1 - p) < (0.13314 : ℝ) := by
  have hh := h.primitive_upper_after_half hL hLP (r := 1 - p)
    ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hpq := mul_nonneg (show 0 ≤ (1 - p) - 0.64 by linarith [hp.2])
    (show 0 ≤ (1 - p) + 0.64 - 2 * lam by linarith [hL.2, hp.2])
  unfold linePrimitive at hh
  nlinarith [hL.2]

theorem initial_R_sharp_upper (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    activationPrimitive phi p < (0.119 : ℝ) := by
  have hL0 : 0 < lam := by linarith [hL.1]
  have hL1 : lam < 1 := by linarith [hL.2]
  have hpI : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hcomp : 1 - p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hR := h.primitive_pos hL0 hL1 p hpI
  have hP := h.primitive_pos hL0 hL1 (1 - p) hcomp
  have hPhi := h.primitive_complement_upper hL hLP hp
  have hbinary := h.two_class_all hL0 hL1 (1 - p) 0 hcomp le_rfl hcomp.1.le hL0.le
  simp only [sub_sub_cancel, add_zero, activationPrimitive, intervalIntegral.integral_same, sub_zero] at hbinary
  change (1 - p) * activationPrimitive phi p ≤ lam * activationPrimitive phi (1 - p) at hbinary
  have hprod := mul_le_mul hL.2 hPhi.le hP.le (by norm_num : (0 : ℝ) ≤ 0.562330)
  have hlow := mul_le_mul_of_nonneg_right (show (0.64 : ℝ) ≤ 1 - p by linarith [hp.2]) hR.le
  nlinarith

/-- Simultaneous bounds after any common low-rank gain and bounded additional
middle-rank gain. This includes both phases and every linear interpolation. -/
theorem bounded_slack_phase_boxes (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p x y eta delta : ℝ}
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hx : x ∈ Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Icc (0.285 : ℝ) 0.38)
    (heta : eta ∈ Icc (0 : ℝ) (2.98 * 0.00025509854))
    (hdelta : delta ∈ Icc (0 : ℝ) 0.00025509854) :
    (0.0826 < activationPrimitive phi p + eta ∧ activationPrimitive phi p + eta < 0.136) ∧
    (0 < activationPrimitive phi (1 - p) + eta + delta ∧
      activationPrimitive phi (1 - p) + eta + delta < 0.135) ∧
    0.0519 < (2 * lam - x) * (activationPrimitive phi p + eta) -
      (p + y - lam) * (activationPrimitive phi (1 - p) + eta + delta) ∧
    0.0143 < lam * (activationPrimitive phi p + eta) -
      p * (activationPrimitive phi (1 - p) + eta + delta) := by
  have hRlo := h.primitive_low_rank_lower hL hLP hp
  have hRhi := h.initial_R_sharp_upper hL hLP hp
  have hPhi := h.initial_complement_sharp_upper hL hLP hp
  have hPlo := h.primitive_pos (by linarith [hL.1]) (by linarith [hL.2]) (1 - p)
    ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hD := h.initial_determinant_margin hL hLP hp hx hy
  have hB := h.initial_binary_margin hL hLP hp
  have hDgain := mul_nonneg (show 0 ≤ 3 * lam - x - p - y by linarith [hL.1, hx.2, hp.2, hy.2]) heta.1
  have hDloss := mul_le_mul (show p + y - lam ≤ 0.178 by linarith [hp.2, hy.2, hL.1])
    hdelta.2 hdelta.1 (by norm_num : (0 : ℝ) ≤ 0.178)
  have hBgain := mul_nonneg (show 0 ≤ lam - p by linarith [hL.1, hp.2]) heta.1
  have hBloss := mul_le_mul hp.2 hdelta.2 hdelta.1 (by norm_num : (0 : ℝ) ≤ 0.36)
  refine ⟨⟨by linarith [heta.1], by linarith [heta.2]⟩,
    ⟨by linarith [heta.1, hdelta.1], by linarith [heta.2, hdelta.2]⟩, ?_, ?_⟩
  · nlinarith only [hD, hDgain, hDloss]
  · nlinarith only [hB, hBgain, hBloss]

end NormalizedNecessaryTwoClass

/-- The stronger K box used during continuation needs only the integrated
ceiling, a primitive ceiling for the middle point, and the quadratic lower
bound for the high state. -/
theorem continuation_gap_bounds {lam p z Jm Y : ℝ}
    (hL : Certificates.Compact.LambdaRange lam)
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hz : z ∈ Icc (0.775 : ℝ) 0.875)
    (hmid : Jm ≤ linePrimitive lam (z - p))
    (hhigh : linePrimitive lam z - linePrimitive lam 1 ≤ Y)
    (hceiling : Y - Jm ≤ lam * p - (z^2 - (z - p)^2) / 2) :
    0 < Jm - Y ∧ Jm - Y < (0.111315 : ℝ) := by
  constructor
  · have hh := mul_pos (show 0 < p by linarith [hp.1])
      (show 0 < z - lam - p / 2 by linarith [hz.1, hL.2, hp.2])
    nlinarith
  · have hzsq := mul_nonneg (show 0 ≤ 0.875 - z by linarith [hz.2])
      (show 0 ≤ 0.875 + z - 2 * lam by linarith [hz.1, hL.2])
    have hLsq := mul_nonneg (show 0 ≤ 0.562330 - lam by linarith [hL.2])
      (show 0 ≤ 2 + lam + 0.562330 - 2 * 0.875 by linarith [hL.1])
    unfold linePrimitive at hmid hhigh
    nlinarith [sq_nonneg (p - (z - lam))]

/-- The first control coefficient remains positive throughout the phase boxes. -/
theorem phase_control_coefficients_positive {lam p x y z R P K : ℝ}
    (hL : Certificates.Compact.LambdaRange lam)
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hx : x ∈ Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Icc (0.285 : ℝ) 0.38) (hz : z ∈ Icc (0.775 : ℝ) 0.875)
    (hR : 0.0826 < R) (hP : 0 < P) (hK : 0 < K ∧ K < 0.111315) :
    (0.0145 : ℝ) < (z - lam) * R + (p + y - lam) * K ∧
      0 < (z - lam) * P + (2 * lam - x) * K := by
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

/-- Recover the post-flattening scalar lower bound from the binary test and the
flat complementary rank. A mere bound on the amount drained would not suffice. -/
theorem scalar_lower_from_flat_binary {lam S R : ℝ}
    (hL : Certificates.Compact.LambdaRange lam)
    (hR : linePrimitive lam 0.307 - S ≤ R)
    (hbinary : (0.693 : ℝ) * R ≤ lam * (linePrimitive lam 0.693 - S)) :
    Certificates.Compact.scalarLower ≤ S := by
  have hden : 0 < (0.693 : ℝ) - lam := by linarith [hL.2]
  have hnum : Certificates.Compact.scalarLower * (0.693 - lam) ≤
      0.693 * linePrimitive lam 0.307 - lam * linePrimitive lam 0.693 := by
    have hfirst : 0 ≤ (0.562330 : ℝ) - lam := by linarith [hL.2]
    have hsecond : 0 ≤ (0.693 : ℝ) * (0.562330 + lam) -
        (0.4528755 + Certificates.Compact.scalarLower) := by
      norm_num [Certificates.Compact.scalarLower]
      linarith [hL.1]
    have hh := mul_nonneg hfirst hsecond
    unfold linePrimitive Certificates.Compact.scalarLower at *
    nlinarith only [hh]
  have hrscaled := mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 0.693)
  apply le_of_mul_le_mul_right (a := (0.693 : ℝ) - lam) ?_ hden
  nlinarith only [hnum, hrscaled, hbinary]

end OptimalG
