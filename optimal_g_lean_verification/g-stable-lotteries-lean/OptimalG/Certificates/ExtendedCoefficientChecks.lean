import OptimalG.Certificates.ExtendedCoefficientData.AlphaSlackHi
import OptimalG.Certificates.ExtendedCoefficientData.AlphaSlackLo
import OptimalG.Certificates.ExtendedCoefficientData.ThetaSlackHi
import OptimalG.Certificates.ExtendedCoefficientData.ThetaSlackLo
import OptimalG.ExtendedCoefficientGeometry
import OptimalG.Certificates.ExtendedCoefficientData.BinaryGap
import OptimalG.Certificates.ExtendedCoefficientData.EtaDecreaseLo
import OptimalG.Certificates.ExtendedCoefficientData.EtaDecreaseHi
import OptimalG.Certificates.ExtendedCoefficientData.MassSlackLo
import OptimalG.Certificates.ExtendedCoefficientData.MassSlackHi
import OptimalG.Certificates.ExtendedCoefficientData.FirstSplitLo
import OptimalG.Certificates.ExtendedCoefficientData.FirstSplitHi
import OptimalG.Certificates.ExtendedCoefficientData.LocalSplitLo
import OptimalG.Certificates.ExtendedCoefficientData.LocalSplitHi

/-! Actual coefficient signs obtained from eight exact endpoint-polynomial
certificates. The dependence on the support-line crossing is affine. -/
namespace OptimalG.Certificates.ExtendedCoefficientChecks
open Set Variational ExtendedScalarExpressions

private theorem affine_endpoint_positive {f : ℝ→ℝ} {a b x : ℝ}
    (hab : a<b) (hx : x∈Icc a b) (ha : 0<f a) (hb : 0<f b)
    (hid : (b-a)*f x=(b-x)*f a+(x-a)*f b) : 0<f x := by
  by_cases hxa : x=a
  · simpa only [hxa] using ha
  have hp : 0<x-a := sub_pos.mpr (lt_of_le_of_ne hx.1 (Ne.symm hxa))
  have h1 := mul_nonneg (sub_nonneg.mpr hx.2) ha.le
  have h2 := mul_pos hp hb
  have hh : 0<(b-a)*f x := by rw [hid]; linarith only [h1,h2]
  exact (mul_pos_iff_of_pos_left (sub_pos.mpr hab)).mp hh

theorem etaDecrease_pos {lam S p t : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) (56233/100000)) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    0<etaDecrease lam S p t := by
  have hlo := ExtendedCoefficientData.EtaDecreaseLo.numerator_pos hL hS hp
  have hhi := ExtendedCoefficientData.EtaDecreaseHi.numerator_pos hL hS hp
  rw [ExtendedCoefficientData.EtaDecreaseLo.expression_identity] at hlo
  rw [ExtendedCoefficientData.EtaDecreaseHi.expression_identity] at hhi
  apply affine_endpoint_positive (by norm_num : (1529/5000:ℝ)<9/25) ht hlo hhi
  simp only [etaDecrease,denominator,etaNumerator,betaNumerator,denominatorDerivative,etaNumeratorDerivative,Variational.quadratic]
  ring

theorem massSlack_pos {lam S p t : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) (56233/100000)) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    0<massSlack lam S p t := by
  have hlo := ExtendedCoefficientData.MassSlackLo.numerator_pos hL hS hp
  have hhi := ExtendedCoefficientData.MassSlackHi.numerator_pos hL hS hp
  rw [ExtendedCoefficientData.MassSlackLo.expression_identity] at hlo
  rw [ExtendedCoefficientData.MassSlackHi.expression_identity] at hhi
  apply affine_endpoint_positive (by norm_num : (1529/5000:ℝ)<9/25) ht hlo hhi
  simp only [massSlack,denominator,etaNumerator,betaNumerator,denominatorDerivative,etaNumeratorDerivative,Variational.quadratic]
  ring

theorem firstSplit_pos {lam S p t : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) (56233/100000)) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    0<firstSplit lam S p t := by
  have hlo := ExtendedCoefficientData.FirstSplitLo.numerator_pos hL hS hp
  have hhi := ExtendedCoefficientData.FirstSplitHi.numerator_pos hL hS hp
  rw [ExtendedCoefficientData.FirstSplitLo.expression_identity] at hlo
  rw [ExtendedCoefficientData.FirstSplitHi.expression_identity] at hhi
  apply affine_endpoint_positive (by norm_num : (1529/5000:ℝ)<9/25) ht hlo hhi
  simp only [firstSplit,denominator,etaNumerator,betaNumerator,denominatorDerivative,etaNumeratorDerivative,Variational.quadratic]
  ring

theorem localSplit_pos {lam S p t : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) (19/50)) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    0<localSplit lam S p t := by
  have hlo := ExtendedCoefficientData.LocalSplitLo.numerator_pos hL hS hp
  have hhi := ExtendedCoefficientData.LocalSplitHi.numerator_pos hL hS hp
  rw [ExtendedCoefficientData.LocalSplitLo.expression_identity] at hlo
  rw [ExtendedCoefficientData.LocalSplitHi.expression_identity] at hhi
  apply affine_endpoint_positive (by norm_num : (1529/5000:ℝ)<9/25) ht hlo hhi
  simp only [localSplit,denominator,etaNumerator,betaNumerator,denominatorDerivative,etaNumeratorDerivative,Variational.quadratic]
  ring

theorem thetaSlack_pos {lam S p t : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) (19/50)) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    0<thetaSlack lam S p t := by
  have hlo := ExtendedCoefficientData.ThetaSlackLo.numerator_pos hL hS hp
  have hhi := ExtendedCoefficientData.ThetaSlackHi.numerator_pos hL hS hp
  rw [ExtendedCoefficientData.ThetaSlackLo.expression_identity] at hlo
  rw [ExtendedCoefficientData.ThetaSlackHi.expression_identity] at hhi
  apply affine_endpoint_positive (by norm_num : (1529/5000:ℝ)<9/25) ht hlo hhi
  simp only [thetaSlack,denominator,etaNumerator,betaNumerator,Variational.quadratic]
  ring

theorem alphaSlack_pos {lam S p t : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) (19/50)) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    0<alphaSlack lam S p t := by
  have hlo := ExtendedCoefficientData.AlphaSlackLo.numerator_pos hL hS hp
  have hhi := ExtendedCoefficientData.AlphaSlackHi.numerator_pos hL hS hp
  rw [ExtendedCoefficientData.AlphaSlackLo.expression_identity] at hlo
  rw [ExtendedCoefficientData.AlphaSlackHi.expression_identity] at hhi
  apply affine_endpoint_positive (by norm_num : (1529/5000:ℝ)<9/25) ht hlo hhi
  simp only [alphaSlack,denominator,etaNumerator,betaNumerator,Variational.quadratic]
  ring

theorem binaryGap_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) lam) : 0<binaryGap lam S p := by
  have hh := ExtendedCoefficientData.BinaryGap.numerator_pos hL hS ⟨hp.1,hp.2.trans hL.2⟩
  rwa [ExtendedCoefficientData.BinaryGap.expression_identity] at hh

 theorem coefficient_bounds {lam S p t : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) lam) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    extendedEta lam p t (Variational.quadratic lam p-S) (Variational.quadratic lam (1-p)-S)≤
      1+extendedBeta lam p t (Variational.quadratic lam p-S) (Variational.quadratic lam (1-p)-S)*p ∧
    1≤extendedBeta lam p t (Variational.quadratic lam p-S) (Variational.quadratic lam (1-p)-S)*
      (SmallMassExpressions.initial lam S-lam+1-p) := by
  have hpbox : p∈Icc (9/25:ℝ) (56233/100000) := ⟨hp.1,hp.2.trans hL.2⟩
  have hN := extended_scalar_denominator_pos hL hS hp ht
  refine ⟨extended_mass_slack_of_polynomial hN (massSlack_pos hL hS hpbox ht).le,?_⟩
  apply extended_split_gap_of_polynomial hN
  have hh := (firstSplit_pos hL hS hpbox ht).le
  unfold firstSplit at hh
  linarith only [hh]

 theorem eta_antitone {lam S t : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    AntitoneOn (fun p => extendedEta lam p t (Variational.quadratic lam p-S) (Variational.quadratic lam (1-p)-S))
      (Icc (9/25:ℝ) lam) := by
  apply extended_scalar_eta_antitone
  · intro p hp
    exact extended_scalar_denominator_pos hL hS hp ht
  · intro p hp
    exact (etaDecrease_pos hL hS ⟨hp.1,hp.2.trans hL.2⟩ ht).le

 theorem eta_le_of_base_system {lam S p t beta0 eta0 : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) lam) (ht : t∈Icc (1529/5000:ℝ) (9/25))
    (hfirst : beta0*(Variational.quadratic lam (1-9/25)-S)+eta0*(lam-t)=2*lam-t)
    (hsecond : beta0*(Variational.quadratic lam (9/25)-S)-eta0*(lam-9/25)=2*(9/25)-lam) :
    extendedEta lam p t (Variational.quadratic lam p-S) (Variational.quadratic lam (1-p)-S)≤eta0 := by
  have hp0 : (9/25:ℝ)∈Icc (9/25:ℝ) lam := ⟨le_rfl,by linarith only [hL.1]⟩
  have hN := extended_scalar_denominator_pos hL hS hp0 ht
  have he := extendedEta_eq_of_system hN.ne' hfirst hsecond
  have hm := eta_antitone hL hS ht hp0 hp hp.1
  dsimp only at hm
  rwa [he] at hm


/-- Actual signed-control ratios for local extended masses. The four endpoint
polynomial checks give the uniform boxes used for tail preservation. -/
theorem local_control_bounds {lam S p t : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) (19/50)) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    denominator lam S p t/etaNumerator lam S p t∈Ioc (0:ℝ) (81/100) ∧
    betaNumerator lam p t/etaNumerator lam S p t∈Ioc (0:ℝ) 3 := by
  have hpL : p∈Icc (9/25:ℝ) lam := ⟨hp.1,by linarith only [hp.2,hL.1]⟩
  have hN := extended_scalar_denominator_pos hL hS hpL ht
  have hbin := binaryGap_pos hL hS hpL
  have hD : 0<etaNumerator lam S p t := by
    have he : etaNumerator lam S p t=denominator lam S p t+binaryGap lam S p := by
      unfold etaNumerator denominator binaryGap
      ring
    rw [he]
    positivity
  have hJ : 0<betaNumerator lam p t := by
    have hm := mul_le_mul ht.2 hp.2 (by linarith only [hp.1]) (by norm_num : (0:ℝ)≤9/25)
    unfold betaNumerator
    nlinarith only [hm,hL.1]
  refine ⟨⟨div_pos hN hD,?_⟩,⟨div_pos hJ hD,?_⟩⟩
  · apply (div_le_iff₀ hD).mpr
    have hh := (thetaSlack_pos hL hS hp ht).le
    unfold thetaSlack at hh
    linarith only [hh]
  · apply (div_le_iff₀ hD).mpr
    have hh := (alphaSlack_pos hL hS hp ht).le
    unfold alphaSlack at hh
    linarith only [hh]

end OptimalG.Certificates.ExtendedCoefficientChecks
