import OptimalG.RelocationRegularity
import OptimalG.PhaseBinaryComparison
import OptimalG.UniversalPhaseBoxes
import OptimalG.VariationalDefs

/-! Binary feasibility and the scalar range of the actual relocated primitive. -/
namespace OptimalG.Relocation
open Set

noncomputable def finalScalar (lam : ℝ) (phi : ℝ → ℝ) : ℝ :=
  slack lam phi 0.38-prefixGain lam phi

variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

theorem first_complement_binary (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.38) :
    (1-p)*firstPrimitive lam phi p ≤ lam*firstPrimitive lam phi (1-p) := by
  have hL0 : 0 < lam := by linarith [hL.1]
  have hL1 : lam < 1 := by linarith [hL.2]
  have hpI : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1],by linarith [hp.2]⟩
  have hcI : 1-p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.2],by linarith [hp.1]⟩
  have hb := h.two_class_all hL0 hL1 (1-p) 0 hcI le_rfl hcI.1.le hL0.le
  have hb' := h.two_class_all hL0 hL1 p 0 hpI le_rfl hpI.1.le hL0.le
  have hcomp : (1-p)*activationPrimitive phi p ≤ lam*activationPrimitive phi (1-p) := by
    simpa only [sub_sub_cancel,add_zero,activationPrimitive,intervalIntegral.integral_same,sub_zero] using hb
  have hopp : p*activationPrimitive phi (1-p) ≤ lam*activationPrimitive phi p := by
    simpa only [add_zero,activationPrimitive,intervalIntegral.integral_same,sub_zero] using hb'
  have hi := (first_phase_preserves_binary hL hp (mass_budget h hL hLP).1
    (by norm_num : (0 : ℝ) ≤ 1) hcomp hopp).1
  rw [firstPrimitive,firstPrimitive,
    first_low_eq h hL hLP ⟨by linarith [hp.1],hp.2⟩,
    first_after_eq h hL hLP (by linarith [hp.2]),
    slack_eq lam phi ⟨by linarith [hp.1],by linarith [hp.2]⟩,
    slack_eq lam phi ⟨by linarith [hp.2],by linarith [hp.1]⟩]
  unfold cumulativeSlack prefixGain
  nlinarith only [hi]

theorem second_complement_binary (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.38) :
    (1-p)*secondPrimitive lam phi p ≤ lam*secondPrimitive lam phi (1-p) := by
  have hh := first_complement_binary h hL hLP hp
  have hsame : secondPrimitive lam phi p=firstPrimitive lam phi p := by
    rw [secondPrimitive,firstPrimitive,second_low_eq h hL hLP (by linarith [hp.2])]
  have hgain := (second_gain_bounds h hL hLP (1-p)).1
  have hP : firstPrimitive lam phi (1-p) ≤ secondPrimitive lam phi (1-p) := by
    unfold firstPrimitive secondPrimitive
    linarith
  rw [hsame]
  exact hh.trans (mul_le_mul_of_nonneg_left hP (by linarith [hL.1]))

theorem finalScalar_lower (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) : Certificates.Compact.scalarLower ≤ finalScalar lam phi := by
  have hm := second_monotone h hL hLP (by norm_num : (0.307 : ℝ) ≤ 0.38)
  rw [secondSlack_middle h hL hLP (r := 0.38) (by norm_num)] at hm
  have hR : linePrimitive lam 0.307-finalScalar lam phi ≤ secondPrimitive lam phi 0.307 := by
    unfold secondPrimitive finalScalar
    linarith
  have hb0 := second_complement_binary h hL hLP (p := 0.307) (by norm_num)
  have hb : (0.693 : ℝ)*secondPrimitive lam phi 0.307 ≤ lam*secondPrimitive lam phi 0.693 := by
    convert hb0 using 1 <;> norm_num
  rw [secondPrimitive_middle h hL hLP (r := 0.693) (by norm_num)] at hb
  exact scalar_lower_from_flat_binary hL hR hb

theorem finalScalar_upper (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) : finalScalar lam phi ≤ universalScalarUpper lam := by
  have hm := slack_monotone h (by norm_num : (0.38 : ℝ) ≤ 0.5)
  have hh := (h.half_slack_bounds hL hLP).2
  rw [← slack_eq lam phi (r := 0.5) (by norm_num)] at hh
  have hn : 0 ≤ prefixGain lam phi := mul_nonneg (by norm_num) (mass_budget h hL hLP).1
  unfold finalScalar
  linarith

theorem second_cap_before_flat (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.38) :
    secondPrimitive lam phi p ≤ Variational.cap lam (finalScalar lam phi) p := by
  have hb := second_complement_binary h hL hLP hp
  rw [secondPrimitive_middle h hL hLP (r := 1-p)
    ⟨by linarith [hp.2],by linarith [hp.1]⟩] at hb
  have hd : 0 < 1-p := by linarith [hp.2]
  have he : (1-p)*Variational.cap lam (finalScalar lam phi) p =
      lam*(linePrimitive lam (1-p)-finalScalar lam phi) := by
    unfold Variational.cap linePrimitive
    field_simp
    ring
  apply (mul_le_mul_iff_of_pos_left hd).mp
  rw [he]
  exact hb

end OptimalG.Relocation
