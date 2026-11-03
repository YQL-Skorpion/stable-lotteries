import OptimalG.VariationalThetaTests
import OptimalG.VariationalThetaUniform
import OptimalG.TailContact
import OptimalG.Certificates.SupportSlopeData

/-! The finite support-slope polynomial bounds attach to actual active
controls through their supporting inequalities and the primitive cap. -/
namespace OptimalG.Variational
open Set

 theorem supporting_theta_lower_of_test_margin {lam p t s R P f g theta C : ℝ}
    (hp : p < 1) (hP : 0 < P)
    (hcap : (1-p)*R ≤ lam*P)
    (hcoef : f-C*(2*lam-t) ≤ 0)
    (hden : 0 ≤ (2*lam-t)*R+(lam-p-s)*P)
    (hmargin : 0 < lam*f+(1-p)*g-C*((2*lam-t)*lam+(1-p)*(lam-p-s)))
    (htest : R*f+P*g ≤ theta*((2*lam-t)*R+(lam-p-s)*P)) : C < theta := by
  by_contra hn
  have hθ := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hden
  have hneg := mul_le_mul_of_nonpos_right hcap hcoef
  have htest' := mul_le_mul_of_nonneg_left (htest.trans hθ) (by linarith : 0 ≤ 1-p)
  have hpos := mul_pos hP hmargin
  nlinarith only [hneg,htest',hpos]

 theorem Admissible.control_R_binary_cap {lam p : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hp : p ∈ Icc pLo pHi) :
    (1-p)*primitive lam d p ≤ lam*(quadratic lam (1-p)-d.S) := by
  have hp1 : p < 1 := by have hh := hp.2; norm_num [pHi] at hh; linarith
  have hh := mul_le_mul_of_nonneg_left (hd.control_primitive_cap hp) (by linarith : 0 ≤ 1-p)
  have hid : (1-p)*cap lam d.S p=lam*(quadratic lam (1-p)-d.S) := by
    unfold cap quadratic
    field_simp [ne_of_gt (sub_pos.mpr hp1)]
    ring
  rwa [hid] at hh

 theorem Admissible.support_test_den_positive {lam p t s : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hp : p ∈ Icc pLo pHi)
    (ht : t ≤ (0.292:ℝ)) (hs : s ≤ (0.36:ℝ)) :
    0 < (2*lam-t)*primitive lam d p+(lam-p-s)*(quadratic lam (1-p)-d.S) := by
  have hL := hd.compact_lambdaRange
  have hR := hd.control_R_lower hp
  have hP := hd.control_P_bounds hp
  have hpr : p ≤ (0.36:ℝ) := by convert! hp.2 using 1 <;> norm_num [pHi]
  have hmR := mul_le_mul_of_nonneg_right (show (0.832:ℝ) ≤ 2*lam-t by linarith [hL.1])
    (show 0 ≤ primitive lam d p by linarith)
  have hMR := mul_le_mul_of_nonneg_left hR (by norm_num : (0:ℝ) ≤ 0.832)
  have hmP := mul_le_mul_of_nonneg_right (show -(0.158:ℝ) ≤ lam-p-s by linarith [hL.1]) hP.1
  have hMP := mul_le_mul_of_nonpos_left hP.2 (by norm_num : -(0.158:ℝ) ≤ 0)
  nlinarith only [hmR,hMR,hmP,hMP]

 theorem active_feature_theta_lower_from_tests {lam z u t s C g : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v=vectorField lam d z u)
    (ht : t ∈ Icc (0.285:ℝ) 0.292) (hs : s ≤ (0.36:ℝ))
    (hC : (0.68:ℝ) ≤ C)
    (hgraphT : (t,capScore lam d.S t) ∈ rankScoreSupport d.phi)
    {score : ℝ} (hgraphS : (s,score) ∈ rankScoreSupport d.phi)
    (hps : v.1.1 ≤ s) (hg : g ≤ score)
    (hmargin : 0 < lam*capScore lam d.S t+(1-v.1.1)*g-
      C*((2*lam-t)*lam+(1-v.1.1)*(lam-v.1.1-s))) :
    C < featureTheta lam d v := by
  have hp := (hd.controlFeatureSupport_subset hv).1.1
  have hP := hd.control_P_lower_uniform hp
  have hL := hd.compact_lambdaRange
  have ht1 : t < 1 := by linarith [ht.2]
  have hfrac : 0 ≤ lam*d.S/(1-t)^2 := div_nonneg
    (mul_nonneg (by linarith [hL.1]) (by linarith [hd.slack_lower])) (sq_nonneg _)
  have hco := mul_le_mul_of_nonneg_right hC
    (show 0 ≤ 2*lam-t by linarith [hL.1,ht.2])
  have hcoef : capScore lam d.S t-C*(2*lam-t) ≤ 0 := by
    unfold capScore
    nlinarith only [hfrac,hco,hL.1,ht.2]
  apply supporting_theta_lower_of_test_margin
    (by have hh := hp.2; norm_num [pHi] at hh; linarith)
    (by linarith : 0 < quadratic lam (1-v.1.1)-d.S)
    (hd.control_R_binary_cap hp) hcoef
    (hd.support_test_den_positive hp ht.2 hs).le hmargin
  have hh := active_feature_theta_test_bound hd hz huLow huHigh hv hactive hgraphT hgraphS hps
  have hhg := mul_le_mul_of_nonneg_left hg (by linarith : 0 ≤ quadratic lam (1-v.1.1)-d.S)
  dsimp only at hh
  linarith


 theorem capScore_antitone_scalar {lam S S' t : ℝ} (hL : 0 ≤ lam) (hS : S ≤ S') :
    capScore lam S' t ≤ capScore lam S t := by
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS hL) (sq_nonneg (1-t))
  unfold capScore
  linarith

 theorem support_margin_early_of_scalar_upper {lam S t C p : ℝ}
    (hL : 0 ≤ lam) (hp : p ≤ 1) (hS : S ≤ (0.023354:ℝ))
    (hchecked : (0.000001:ℝ) ≤ lam*capScore lam 0.023354 t+(1-p)*capScore lam 0.023354 t-
      C*((2*lam-t)*lam+(1-p)*(lam-p-t))) :
    0 < lam*capScore lam S t+(1-p)*capScore lam S t-
      C*((2*lam-t)*lam+(1-p)*(lam-p-t)) := by
  have hc := capScore_antitone_scalar (t:=t) hL hS
  have h1 := mul_le_mul_of_nonneg_left hc hL
  have h2 := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hp)
  linarith

 theorem support_margin_late_of_scalar_upper {lam S t C p : ℝ}
    (hL : 0 ≤ lam) (hS : S ≤ (0.023354:ℝ))
    (hchecked : (0.000001:ℝ) ≤ lam*capScore lam 0.023354 t+(1-p)*(lam-p-0.022)-
      C*((2*lam-t)*lam+(1-p)*(lam-p-p))) :
    0 < lam*capScore lam S t+(1-p)*(lam-p-0.022)-
      C*((2*lam-t)*lam+(1-p)*(lam-p-p)) := by
  have hc := capScore_antitone_scalar (t:=t) hL hS
  have h1 := mul_le_mul_of_nonneg_left hc hL
  linarith

 theorem active_feature_theta_lower_from_cap_and_band {lam z u t C : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v=vectorField lam d z u)
    (ht : t ∈ Icc (0.285:ℝ) 0.292) (hC : (0.68:ℝ) ≤ C)
    (hgraphT : (t,capScore lam d.S t) ∈ rankScoreSupport d.phi)
    (hband : ∀ p ∈ Icc t pHi,∃ score,(p,score) ∈ rankScoreSupport d.phi ∧ lam-p-0.022 ≤ score)
    (hearly : ∀ p ∈ Icc pLo t,0 < lam*capScore lam d.S t+(1-p)*capScore lam d.S t-
      C*((2*lam-t)*lam+(1-p)*(lam-p-t)))
    (hlate : ∀ p ∈ Icc t pHi,0 < lam*capScore lam d.S t+(1-p)*(lam-p-0.022)-
      C*((2*lam-t)*lam+(1-p)*(lam-p-p))) :
    C < featureTheta lam d v := by
  have hp := (hd.controlFeatureSupport_subset hv).1.1
  by_cases hpt : v.1.1 ≤ t
  · exact active_feature_theta_lower_from_tests hd hz huLow huHigh hv hactive ht
      (by linarith [ht.2]) hC hgraphT hgraphT hpt le_rfl (hearly _ ⟨hp.1,hpt⟩)
  · obtain ⟨score,hgraph,hscore⟩ := hband _ ⟨(le_of_not_ge hpt),hp.2⟩
    exact active_feature_theta_lower_from_tests hd hz huLow huHigh hv hactive ht
      (by convert! hp.2 using 1 <;> norm_num [pHi]) hC hgraphT hgraph le_rfl hscore
      (hlate _ ⟨(le_of_not_ge hpt),hp.2⟩)

 theorem active_feature_theta_gt_6809 {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S ≤ (0.023354:ℝ))
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v=vectorField lam d z u)
    (hgraph : ((0.2854:ℝ),capScore lam d.S 0.2854) ∈ rankScoreSupport d.phi)
    (hband : ∀ p ∈ Icc (0.2854:ℝ) pHi,∃ score,(p,score) ∈ rankScoreSupport d.phi ∧ lam-p-0.022 ≤ score) :
    (0.6809:ℝ) < featureTheta lam d v := by
  apply active_feature_theta_lower_from_cap_and_band hd hz huLow huHigh hv hactive
    (t:=0.2854) (by norm_num) (by norm_num) hgraph hband
  · intro p hp
    apply support_margin_early_of_scalar_upper (by linarith [hd.compact_lambdaRange.1])
      (by linarith [hp.2]) hS
    convert! Certificates.SupportSlopeData.step0_0_margin (p:=p) hd.compact_lambdaRange
      (by convert! hp using 1 <;> norm_num [pLo]) using 1 <;> norm_num [capScore]
  · intro p hp
    apply support_margin_late_of_scalar_upper (by linarith [hd.compact_lambdaRange.1]) hS
    convert! Certificates.SupportSlopeData.step0_1_margin (p:=p) hd.compact_lambdaRange
      (by convert! hp using 1 <;> norm_num [pHi]) using 1 <;> norm_num [capScore]

 theorem active_feature_theta_gt_6907 {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S ≤ (0.023354:ℝ))
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v=vectorField lam d z u)
    (hgraph : ((0.2913:ℝ),capScore lam d.S 0.2913) ∈ rankScoreSupport d.phi)
    (hband : ∀ p ∈ Icc (0.2913:ℝ) pHi,∃ score,(p,score) ∈ rankScoreSupport d.phi ∧ lam-p-0.022 ≤ score) :
    (0.6907:ℝ) < featureTheta lam d v := by
  apply active_feature_theta_lower_from_cap_and_band hd hz huLow huHigh hv hactive
    (t:=0.2913) (by norm_num) (by norm_num) hgraph hband
  · intro p hp
    apply support_margin_early_of_scalar_upper (by linarith [hd.compact_lambdaRange.1])
      (by linarith [hp.2]) hS
    convert! Certificates.SupportSlopeData.step1_0_margin (p:=p) hd.compact_lambdaRange
      (by convert! hp using 1 <;> norm_num [pLo]) using 1 <;> norm_num [capScore]
  · intro p hp
    apply support_margin_late_of_scalar_upper (by linarith [hd.compact_lambdaRange.1]) hS
    convert! Certificates.SupportSlopeData.step1_1_margin (p:=p) hd.compact_lambdaRange
      (by convert! hp using 1 <;> norm_num [pHi]) using 1 <;> norm_num [capScore]

 theorem active_feature_theta_gt_691 {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S ≤ (0.023354:ℝ))
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v=vectorField lam d z u)
    (hgraph : ((0.2918:ℝ),capScore lam d.S 0.2918) ∈ rankScoreSupport d.phi)
    (hband : ∀ p ∈ Icc (0.2918:ℝ) pHi,∃ score,(p,score) ∈ rankScoreSupport d.phi ∧ lam-p-0.022 ≤ score) :
    (0.691:ℝ) < featureTheta lam d v := by
  apply active_feature_theta_lower_from_cap_and_band hd hz huLow huHigh hv hactive
    (t:=0.2918) (by norm_num) (by norm_num) hgraph hband
  · intro p hp
    apply support_margin_early_of_scalar_upper (by linarith [hd.compact_lambdaRange.1])
      (by linarith [hp.2]) hS
    convert! Certificates.SupportSlopeData.step2_0_margin (p:=p) hd.compact_lambdaRange
      (by convert! hp using 1 <;> norm_num [pLo]) using 1 <;> norm_num [capScore]
  · intro p hp
    apply support_margin_late_of_scalar_upper (by linarith [hd.compact_lambdaRange.1]) hS
    convert! Certificates.SupportSlopeData.step2_1_margin (p:=p) hd.compact_lambdaRange
      (by convert! hp using 1 <;> norm_num [pHi]) using 1 <;> norm_num [capScore]


/-- This form applies to balanced supporting controls even when they are
not attained minimizers of the continuation field. -/
 theorem Admissible.theta_gt_691_of_test_bounds {lam p theta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S≤(0.023354:ℝ)) (hp : p∈Icc pLo pHi)
    (hearly : p≤(0.2918:ℝ) →
      primitive lam d p*capScore lam d.S 0.2918+
        (quadratic lam (1-p)-d.S)*capScore lam d.S 0.2918 ≤
      theta*((2*lam-0.2918)*primitive lam d p+(lam-p-0.2918)*(quadratic lam (1-p)-d.S)))
    (hlate : (0.2918:ℝ)≤p →
      primitive lam d p*capScore lam d.S 0.2918+
        (quadratic lam (1-p)-d.S)*(lam-p-0.022) ≤
      theta*((2*lam-0.2918)*primitive lam d p+(lam-p-p)*(quadratic lam (1-p)-d.S))) :
    (0.691:ℝ)<theta := by
  have hL := hd.compact_lambdaRange
  have hP := hd.control_P_lower_uniform hp
  have hL0 : 0≤lam := by linarith [hL.1]
  have hfrac : 0≤lam*d.S/(1-(0.2918:ℝ))^2 := div_nonneg
    (mul_nonneg hL0 (by linarith [hd.slack_lower])) (sq_nonneg _)
  have hcoef : capScore lam d.S 0.2918-0.691*(2*lam-0.2918)≤0 := by
    unfold capScore
    nlinarith only [hfrac,hL.1]
  have hp1 : p<1 := by have hh := hp.2; norm_num [pHi] at hh;linarith
  have hP0 : 0<quadratic lam (1-p)-d.S := by linarith
  have hcap := hd.control_R_binary_cap hp
  by_cases hpt : p≤(0.2918:ℝ)
  · apply supporting_theta_lower_of_test_margin hp1 hP0 hcap hcoef
      (hd.support_test_den_positive hp (by norm_num) (by norm_num)).le _ (hearly hpt)
    apply support_margin_early_of_scalar_upper hL0 hp1.le hS
    convert! Certificates.SupportSlopeData.step2_0_margin (p:=p) hL
      (by convert! And.intro hp.1 hpt using 1 <;> norm_num [pLo]) using 1 <;> norm_num [capScore]
  · apply supporting_theta_lower_of_test_margin hp1 hP0 hcap hcoef
      (hd.support_test_den_positive hp (by norm_num)
        (by convert! hp.2 using 1 <;> norm_num [pHi])).le _ (hlate (le_of_not_ge hpt))
    apply support_margin_late_of_scalar_upper hL0 hS
    convert! Certificates.SupportSlopeData.step2_1_margin (p:=p) hL
      (by convert! And.intro (le_of_not_ge hpt) hp.2 using 1 <;> norm_num [pHi]) using 1 <;> norm_num [capScore]

end OptimalG.Variational
