import OptimalG.VariationalPositiveScores
import OptimalG.ParameterTransferGeometry

/-! A positive active supporting slope follows already from the compact
admissible box and the proved active-score lower bounds. This removes an
unnecessary dependence on the finer reference localization at this step. -/
namespace OptimalG.Variational
open Set

 theorem Admissible.control_P_lower_uniform {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {p : ℝ} (hp : p ∈ Icc pLo pHi) :
    (0.11379 : ℝ) ≤ quadratic lam (1-p)-d.S := by
  have hL := hd.compact_lambdaRange
  have hS := hd.slack_upper
  have hp' : p ∈ Icc (0.25 : ℝ) 0.36 := by
    convert! hp using 1 <;> norm_num [pLo,pHi]
  have hLq := mul_nonneg (sub_nonneg.mpr hL.1) (show 0 ≤ 1-p by linarith [hp'.2])
  have hbox := mul_nonneg (show 0 ≤ (1-p)-0.64 by linarith [hp'.2])
    (show 0 ≤ 0.75-(1-p) by linarith [hp'.1])
  unfold quadratic
  nlinarith only [hLq,hbox,hS,hp'.1]

 theorem Admissible.control_determinant_upper_uniform {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {v : Control} (hv : v ∈ controlDomain) :
    controlDeterminant lam d v ≤ (0.106 : ℝ) := by
  have hL := hd.compact_lambdaRange
  obtain ⟨hp,hx,hy⟩ := ParameterTransfer.control_ranges hv
  have hR0 := hd.control_R_lower hv.1
  have hR1 := ParameterTransfer.Admissible_control_R_small hd hv.1
  have hP := hd.control_P_bounds hv.1
  have hh := mul_le_mul (show 2*lam-v.2.1 ≤ (0.84 : ℝ) by linarith [hL.2,hx.1])
    hR1.le (by linarith : 0 ≤ primitive lam d v.1) (by norm_num : (0 : ℝ) ≤ 0.84)
  have hk := mul_le_mul_of_nonneg_right
    (show -(v.1+v.2.2-lam) ≤ (0.028 : ℝ) by linarith [hp.1,hy.1,hL.2]) hP.1
  have hkp := mul_le_mul_of_nonneg_left hP.2 (by norm_num : (0 : ℝ) ≤ 0.028)
  unfold controlDeterminant
  nlinarith only [hh,hk,hkp]

 theorem active_feature_theta_gt_uniform {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v=vectorField lam d z u) :
    (0.129 : ℝ) < featureTheta lam d v := by
  have hc := (hd.controlFeatureSupport_subset hv).1
  have hscore := active_feature_scores_positive hd hz huLow huHigh hv hactive
  have hR := hd.control_R_lower hc.1
  have hP := hd.control_P_lower_uniform hc.1
  have hD := hd.control_determinant_upper_uniform hc
  have hDp : 0 < controlDeterminant lam d v.1 := by linarith [hd.determinant_positive hc]
  have hRA := mul_le_mul_of_nonneg_left hscore.1.le
    (show 0 ≤ primitive lam d v.1.1 by linarith)
  have hPB := mul_le_mul_of_nonneg_left hscore.2.le
    (show 0 ≤ quadratic lam (1-v.1.1)-d.S by linarith)
  unfold featureTheta Certificates.Control.theta
  change (0.129 : ℝ) < (primitive lam d v.1.1*v.2.1+
    (quadratic lam (1-v.1.1)-d.S)*v.2.2)/controlDeterminant lam d v.1
  apply (lt_div_iff₀ hDp).mpr
  nlinarith only [hR,hP,hD,hRA,hPB]

end OptimalG.Variational
