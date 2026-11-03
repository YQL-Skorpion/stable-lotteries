import OptimalG.Certificates.StaticSmallMassLinks.DirectTarget
import OptimalG.Certificates.StaticSmallMassLinks.DirectSplitMargin
import OptimalG.Certificates.StaticSmallMassLinksBatch02
import OptimalG.Certificates.StaticSmallMassLinksBatch03
import OptimalG.Certificates.StaticSmallMassLinksBatch04
import OptimalG.Certificates.SmallMassDenominators
import OptimalG.IntermediateSmallMass

/-! The finite C4 signs imply all seven actual intermediate-strip checks. -/
namespace OptimalG.Certificates.SmallMassExpressions
open Set

theorem static_intermediate_checks {phi : ℝ→ℝ} {p : ℝ}
    (h : VerifierCurve phi (StaticLow.lam:ℝ))
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (1/25:ℝ) (7/50))
    (hhead : ∀ r∈Icc (0:ℝ) (527/2000),phi r=score (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r)
    (hcap : phi (7/25)=cap28 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) :
    IntermediateSmallMassChecks phi (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p := by
  have hD := denominator_pos hL hS (p:=p) ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  have hF : 0 < initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) := by have hh := initial_bounds hL hS; linarith only [hh.1]
  have hM := cap28_pos hL hS
  have hW := cap2918_pos hL hS
  have h_target := StaticSmallMassLinks.DirectTarget.coefficient_positive hL hS hp hD hF hM hW
  have h_split_margin := StaticSmallMassLinks.DirectSplitMargin.coefficient_positive hL hS hp hD hF hM hW
  have h_beta_mass := StaticSmallMassLinks.DirectBetaMass.coefficient_positive hL hS hp hD hF hM hW
  have h_defect_coefficient_1 := StaticSmallMassLinks.DirectDefectCoefficient1.coefficient_positive hL hS hp hD hF hM hW
  have h_endpoint_switch_1 := StaticSmallMassLinks.DirectEndpointSwitch1.coefficient_positive hL hS hp hD hF hM hW
  have h_endpoint_one_1 := StaticSmallMassLinks.DirectEndpointOne1.coefficient_positive hL hS hp hD hF hM hW
  have h_head_zero_2 := StaticSmallMassLinks.DirectHeadZero2.coefficient_positive hL hS hp hD hF hM hW
  have h_defect_coefficient_2 := StaticSmallMassLinks.DirectDefectCoefficient2.coefficient_positive hL hS hp hD hF hM hW
  have h_endpoint_switch_2 := StaticSmallMassLinks.DirectEndpointSwitch2.coefficient_positive hL hS hp hD hF hM hW
  have h_endpoint_one_2 := StaticSmallMassLinks.DirectEndpointOne2.coefficient_positive hL hS hp hD hF hM hW
  have hzero : phi 0=initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) := by
    simpa [score] using hhead 0 ⟨le_rfl,by norm_num⟩
  have hpr : p∈Icc (0:ℝ) (527/2000) := ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  obtain ⟨hden,hbeta,htarget,hbd,htd⟩ := coefficients_agree
    (affine_head_agrees h hhead p hpr) (hhead p hpr)
  have heta : intermediateSmallEta phi (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p=min (etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) (etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) := by
    simp only [intermediateSmallEta,smallMassCapEta,hbeta,htarget,hcap,etaOne,etaTwo]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hbeta]
    linarith only [h_beta_mass]
  · rw [htarget]
    linarith only [h_target]
  · rw [heta,hzero,htarget]
    have hh := mul_le_mul_of_nonneg_right (min_le_right (etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) (etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)) hF.le
    linarith only [hh,h_head_zero_2]
  · rw [hbeta,hzero]
    linarith only [h_split_margin]
  · rw [hbeta,heta]
    rcases le_total (etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) (etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) with he|he
    · rw [min_eq_left he]
      nlinarith only [h_defect_coefficient_1]
    · rw [min_eq_right he]
      nlinarith only [h_defect_coefficient_2]
  · rw [hbeta,heta]
    rcases le_total (etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) (etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) with he|he
    · rw [min_eq_left he]
      norm_num [smallMassDefectProxy]
      nlinarith only [h_endpoint_switch_1]
    · rw [min_eq_right he]
      norm_num [smallMassDefectProxy]
      nlinarith only [h_endpoint_switch_2]
  · rw [hbeta,heta]
    rcases le_total (etaOne (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) (etaTwo (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) with he|he
    · rw [min_eq_left he]
      norm_num [smallMassDefectProxy]
      nlinarith only [h_endpoint_one_1]
    · rw [min_eq_right he]
      norm_num [smallMassDefectProxy]
      nlinarith only [h_endpoint_one_2]

end OptimalG.Certificates.SmallMassExpressions
