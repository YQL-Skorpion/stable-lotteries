import OptimalG.Certificates.StaticSmallMassLinksBatch01
import OptimalG.Certificates.StaticSmallMassLinksBatch00
import OptimalG.Certificates.StaticSmallMassLinksBatch02
import OptimalG.Certificates.StaticSmallMassLinks.CapRateRight
import OptimalG.Certificates.SmallMassDenominators
import OptimalG.TransportSmallMass

/-! The finite C4 signs imply the actual derivative-transport checks. -/
namespace OptimalG.Certificates.SmallMassExpressions
open Set

theorem static_cap_transport_checks {phi : ℝ→ℝ} {p : ℝ}
    (h : VerifierCurve phi (StaticLow.lam:ℝ))
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (1/5:ℝ) (527/2000))
    (hhead : ∀ r∈Icc (0:ℝ) (527/2000),phi r=score (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r)
    (hw : phi (1459/5000)=cap2918 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) :
    TransportSmallMassChecks phi (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (cap28 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) p := by
  have hD := denominator_pos hL hS (p:=p) ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  have hF : 0 < initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) := by have hh := initial_bounds hL hS; linarith only [hh.1]
  have hM := cap28_pos hL hS
  have hW := cap2918_pos hL hS
  have h_target := StaticSmallMassLinks.CapTarget.coefficient_positive hL hS hp hD hF hM hW
  have h_split_margin := StaticSmallMassLinks.CapSplitMargin.coefficient_positive hL hS hp hD hF hM hW
  have h_beta_derivative := StaticSmallMassLinks.CapBetaDerivative.coefficient_positive hL hS hp hD hF hM hW
  have h_target_derivative := StaticSmallMassLinks.CapTargetDerivative.coefficient_positive hL hS hp hD hF hM hW
  have h_rate_slope := StaticSmallMassLinks.CapRateSlope.coefficient_positive hL hS hp hD hF hM hW
  have h_rate_left := StaticSmallMassLinks.CapRateLeft.coefficient_positive hL hS hp hD hF hM hW
  have h_rate_right := StaticSmallMassLinks.CapRateRight.coefficient_positive hL hS hp hD hF hM hW
  have h_support_witness := StaticSmallMassLinks.CapSupportWitness.coefficient_positive hL hS hp hD hF hM hW
  have h_minimizer_two := StaticSmallMassLinks.CapMinimizerTwo.coefficient_positive hL hS hp hD hF hM hW
  have h_minimizer_head_zero := StaticSmallMassLinks.CapMinimizerHeadZero.coefficient_positive hL hS hp hD hF hM hW
  have hzero : phi 0=initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) := by
    simpa [score] using hhead 0 ⟨le_rfl,by norm_num⟩
  have hpr : p∈Icc (0:ℝ) (527/2000) := ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  obtain ⟨hden,hbeta,htarget,hbd,htd⟩ := coefficients_agree
    (affine_head_agrees h hhead p hpr) (hhead p hpr)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [htarget]
    linarith only [h_target]
  · rw [hbd]
    linarith only [h_beta_derivative]
  · rw [htd]
    linarith only [h_target_derivative]
  · rw [htarget,hbeta,hw]
    have hh : etaWitness (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p≤1+beta (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*p := by linarith only [h_support_witness]
    exact (div_le_iff₀ hW).mp hh
  · rw [hbeta,hzero]
    linarith only [h_split_margin]
  · rw [htd,hbd,hbeta]
    exact h_rate_slope.le
  · rw [htd,hbd,hbeta,←rateLeft_eq]
    exact h_rate_left.le
  · rw [htd,hbd,hbeta,←rateRight_eq]
    exact h_rate_right.le

end OptimalG.Certificates.SmallMassExpressions
