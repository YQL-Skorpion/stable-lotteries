import OptimalG.NecessaryMonotonicity
import OptimalG.UniversalMomentBounds
import OptimalG.Certificates.Compact

/-! # Scalar consequences of the universal LP

The three explicit primitive inequalities below are rounded outward from the
central and half-rank dual conclusions. All interpolation and integral bounds
are proved analytically; no LP checks are assumed to have completed here.
-/
namespace OptimalG
open Set MeasureTheory

/-- Explicit input conclusions from the universal LP; these are actual
primitive bounds, not assumptions about a discretized replacement function. -/
structure UniversalLPPrimitiveBounds (phi : ℝ → ℝ) : Prop where
  central : (-0.001429898539474 : ℝ) ≤ activationPrimitive phi 0.785 - activationPrimitive phi 0.345
  half_lower : (0.1295146851195648 : ℝ) ≤ activationPrimitive phi 0.5
  half_upper : activationPrimitive phi 0.5 ≤ (0.1342007783259218 : ℝ)

noncomputable def activationSlack (lam : ℝ) (phi : ℝ → ℝ) (r : ℝ) : ℝ := lam - r - phi r
noncomputable def cumulativeSlack (lam : ℝ) (phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  linePrimitive lam r - activationPrimitive phi r
noncomputable def universalScalarUpper (lam : ℝ) : ℝ := 0.0266503148804352 - (0.562330 - lam) / 2

namespace NormalizedNecessaryTwoClass
variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

theorem activationSlack_nonneg {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    0 ≤ activationSlack lam phi r := sub_nonneg.mpr (h.ceiling r hr)

theorem cumulativeSlack_nonneg {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    0 ≤ cumulativeSlack lam phi r := sub_nonneg.mpr (h.primitive_upper hr)

theorem slack_integral {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ r in a..b, activationSlack lam phi r) =
      cumulativeSlack lam phi b - cumulativeSlack lam phi a := by
  have hp := (h.continuous.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi : IntervalIntegrable (fun r : ℝ => r) volume a b := continuous_id.intervalIntegrable a b
  unfold activationSlack
  rw [intervalIntegral.integral_sub (intervalIntegrable_const.sub hi) hp,
    intervalIntegral.integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const,
    integral_id, ← h.primitive_increment ha hab hb]
  simp only [smul_eq_mul, cumulativeSlack, linePrimitive]
  ring

theorem cumulativeSlack_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    cumulativeSlack lam phi a ≤ cumulativeSlack lam phi b := by
  have hh := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun r hr => h.activationSlack_nonneg ⟨ha.trans hr.1, hr.2.trans hb⟩)
  rw [h.slack_integral ha hab hb] at hh
  exact sub_nonneg.mp hh

theorem half_slack_bounds (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    (0.02196 : ℝ) < cumulativeSlack lam phi 0.5 ∧
      cumulativeSlack lam phi 0.5 ≤ universalScalarUpper lam := by
  rcases hL with ⟨hlo, hhi⟩
  unfold cumulativeSlack linePrimitive universalScalarUpper
  constructor <;> linarith [hLP.half_lower, hLP.half_upper]

theorem central_slack_bound (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    (∫ r in (0.345 : ℝ)..0.785, activationSlack lam phi r) < (0.00025509854 : ℝ) := by
  rw [h.slack_integral (by norm_num) (by norm_num) (by norm_num)]
  unfold cumulativeSlack linePrimitive
  linarith [hL.2, hLP.central]

/-- Every low-rank primitive is bounded below by the same actual half-rank slack. -/
theorem primitive_lower_before_half (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 0.5) :
    linePrimitive lam r - universalScalarUpper lam ≤ activationPrimitive phi r := by
  have hm := h.cumulativeSlack_mono hr.1 hr.2 (by norm_num)
  have hu := (h.half_slack_bounds hL hLP).2
  unfold cumulativeSlack at hm hu
  linarith

theorem primitive_upper_after_half (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc (0.5 : ℝ) 1) :
    activationPrimitive phi r < linePrimitive lam r - 0.02196 := by
  have hm := h.cumulativeSlack_mono (by norm_num) hr.1 hr.2
  have hl := (h.half_slack_bounds hL hLP).1
  unfold cumulativeSlack at hm hl
  linarith

theorem primitive_low_rank_lower (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    (0.0826 : ℝ) < activationPrimitive phi p := by
  have hh := h.primitive_lower_before_half hL hLP (r := p) ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hpq := mul_nonneg (show 0 ≤ p - 0.25 by linarith [hp.1])
    (show 0 ≤ 2 * lam - p - 0.25 by linarith [hL.1, hp.2])
  unfold linePrimitive universalScalarUpper at hh
  nlinarith [hL.1, hL.2]

theorem primitive_complement_upper (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    activationPrimitive phi (1 - p) < (0.135 : ℝ) := by
  have hr : 1 - p ∈ Icc (0.5 : ℝ) 1 := ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hh := h.primitive_upper_after_half hL hLP hr
  have hpq := mul_nonneg (show 0 ≤ (1 - p) - 0.64 by linarith [hp.2])
    (show 0 ≤ (1 - p) + 0.64 - 2 * lam by linarith [hL.2, hp.2])
  unfold linePrimitive at hh
  nlinarith [hL.2]

theorem primitive_low_rank_upper (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    activationPrimitive phi p < (0.136 : ℝ) := by
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
  have hprod := mul_le_mul (show lam ≤ 0.562330 from hL.2) hPhi.le hP.le (by norm_num : (0 : ℝ) ≤ 0.562330)
  have hlow := mul_le_mul_of_nonneg_right (show (0.64 : ℝ) ≤ 1 - p by linarith [hp.2]) hR.le
  nlinarith

end NormalizedNecessaryTwoClass
end OptimalG
