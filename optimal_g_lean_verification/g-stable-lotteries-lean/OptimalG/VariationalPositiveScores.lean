import OptimalG.VariationalSupportingFeatures

/-! Uniform positivity of genuinely active low scores. A coarse support argument
suffices and avoids the sharper numerical localization used in the paper. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem Admissible.control_R_le_small {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {p : ℝ} (hp : p ∈ Icc pLo pHi) : primitive lam d p ≤ (15:ℝ)/100 := by
  have hcap := hd.control_primitive_cap hp
  have hL0 : (562:ℝ)/1000 ≤ lam := by have hh := hd.1.1; norm_num [lambdaLo] at hh; linarith
  have hL1 : lam ≤ (563:ℝ)/1000 := by have hh := hd.1.2; norm_num [lambdaHi] at hh; linarith
  have hp0 : 0 ≤ p := by have hh := hp.1; norm_num [pLo] at hh; linarith
  have hp1 : p ≤ (36:ℝ)/100 := hp.2
  have hS0 : 0 ≤ d.S := by linarith [hd.slack_lower]
  have hfrac : 0 ≤ lam*d.S/(1-p) := div_nonneg (mul_nonneg (by linarith) hS0) (by linarith)
  have hlsq := mul_self_le_mul_self (by linarith : 0 ≤ lam) hL1
  have hlp := mul_le_mul hL1 hp1 hp0 (by norm_num : (0:ℝ) ≤ 563/1000)
  unfold cap at hcap
  nlinarith

theorem Admissible.determinant_coarse_upper {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {c : Control} (hc : c ∈ controlDomain) : controlDeterminant lam d c ≤ (14:ℝ)/100 := by
  have hR0 : 0 ≤ primitive lam d c.1 := by linarith [hd.control_R_lower hc.1]
  have hR1 := hd.control_R_le_small hc.1
  have hP := hd.control_P_bounds hc.1
  have hL := hd.1.2
  have hx := hc.2.1.1
  have hp := hc.1.1
  have hy := (le_max_left xLo c.1).trans hc.2.2.1
  norm_num [lambdaHi,xLo,pLo] at hL hx hp hy
  have hh : 2*lam-c.2.1 ≤ (84:ℝ)/100 := by linarith
  have hk : -(c.1+c.2.2-lam) ≤ (3:ℝ)/100 := by linarith
  have hhR := mul_le_mul_of_nonneg_right hh hR0
  have hRu := mul_le_mul_of_nonneg_left hR1 (by norm_num : (0:ℝ) ≤ 84/100)
  have hkP := mul_le_mul_of_nonneg_right hk hP.1
  have hPu := mul_le_mul_of_nonneg_left hP.2 (by norm_num : (0:ℝ) ≤ 3/100)
  unfold controlDeterminant
  nlinarith

theorem Admissible.featureTheta_coarse_upper {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {v : ControlFeature} (hv : v ∈ controlFeatureSupport d) :
    featureTheta lam d v < (9:ℝ)/10 := by
  have hc := (hd.controlFeatureSupport_subset hv).1
  have hx := (hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hv).1).2.2
  have hy := (hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hv).2).2.2
  have hR0 : 0 ≤ primitive lam d v.1.1 := by linarith [hd.control_R_lower hc.1]
  have hP0 := (hd.control_P_bounds hc.1).1
  have hxR := mul_le_mul_of_nonneg_left hx hR0
  have hyP := mul_le_mul_of_nonneg_left hy hP0
  have hgap := hd.control_binary_gap hc
  have hDu := hd.determinant_coarse_upper hc
  have hD : 0 < controlDeterminant lam d v.1 := by linarith [hd.determinant_positive hc]
  unfold featureTheta Certificates.Control.theta
  change (primitive lam d v.1.1*v.2.1+(quadratic lam (1-v.1.1)-d.S)*v.2.2) / controlDeterminant lam d v.1 < _
  apply (div_lt_iff₀ hD).mpr
  unfold controlDeterminant at hDu ⊢
  nlinarith

/-- There is an essential graph point of score above .09 in [.36,.38]. -/
theorem Admissible.exists_high_rank_score {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    ∃ w ∈ rankScoreSupport d.phi, w.1 ∈ Icc pHi xHi ∧ (9:ℝ)/100 < w.2 := by
  have hm := Certificates.Compact.low_average_gt lam d.S hd.compact_lambdaRange hd.compact_scalarRange
  have hm' : (9:ℝ)/100 < (quadratic lam xHi-d.S-cap lam d.S pHi)/(2/100) := by
    norm_num [Certificates.Compact.lowAverage,Certificates.quadratic,Certificates.cap,quadratic,cap,xHi,pHi] at hm ⊢
    exact hm
  have hlo := hd.lowPrimitive_lower (show xHi ∈ Icc ell tEnd by norm_num [xHi,ell,tEnd])
  have hhi := hd.lowPrimitive_le_cap (show pHi ∈ Icc ell tEnd by norm_num [pHi,ell,tEnd])
  have hprimitive := hd.lowPrimitive_sub
    (show pHi ∈ Icc ell tEnd by norm_num [pHi,ell,tEnd])
    (show xHi ∈ Icc ell tEnd by norm_num [xHi,ell,tEnd])
  have hsub : Icc pHi xHi ⊆ Icc ell tEnd := by
    apply Icc_subset_Icc <;> norm_num [pHi,xHi,ell,tEnd]
  by_contra hn
  push_neg at hn
  have hb : ∀ᵐ r ∂volume.restrict (Icc pHi xHi), d.phi r ≤ (9:ℝ)/100 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae_restrict_of_subset hsub hd.ae_low_rankScore_mem] with r hr hg
    exact hn (r,d.phi r) (hg ⟨(by norm_num [xLo,pHi] : xLo ≤ pHi).trans hr.1,hr.2⟩) hr
  have hi := intervalIntegral.integral_mono_ae_restrict (by norm_num [pHi,xHi] : pHi ≤ xHi)
    (hd.intervalIntegrable (by norm_num [ell,pHi]) (by norm_num [pHi,xHi]) (by norm_num [xHi,tEnd]))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (9:ℝ)/100) volume pHi xHi) hb
  rw [intervalIntegral.integral_const] at hi
  norm_num [pHi,xHi] at hi hm' hlo hhi hprimitive
  nlinarith only [hi,hm',hlo,hhi,hprimitive]

theorem active_feature_scores_positive {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u)
    (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v = vectorField lam d z u) :
    (7:ℝ)/100 < v.2.1 ∧ (7:ℝ)/100 < v.2.2 := by
  obtain ⟨w,hw,hwr,hws⟩ := hd.exists_high_rank_score
  have hc := (hd.controlFeatureSupport_subset hv).1
  have htheta0 := (hd.featureTheta_bounds hv).1
  have htheta1 := hd.featureTheta_coarse_upper hv
  have hsx := active_feature_supports_x hd hz huLow huHigh hv hactive hw
  have hsy := active_feature_supports_y hd hz huLow huHigh hv hactive hw (hc.1.2.trans hwr.1)
  have hx := hc.2.1.2
  have hy := hc.2.2.2
  have hw0 := hwr.1
  norm_num [pHi,xHi] at hx hy hw0
  have hdx : v.1.2.1-w.1 ≤ (2:ℝ)/100 := by linarith
  have hdy : v.1.2.2-w.1 ≤ (2:ℝ)/100 := by linarith
  have hmx := mul_le_mul_of_nonneg_left hdx htheta0
  have hmy := mul_le_mul_of_nonneg_left hdy htheta0
  constructor <;> nlinarith only [hsx,hsy,hws,htheta1,hmx,hmy]

end OptimalG.Variational
