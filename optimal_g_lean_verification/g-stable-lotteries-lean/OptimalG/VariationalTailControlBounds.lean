import OptimalG.VariationalTerminalCoefficients
import OptimalG.VariationalContactTailConsequences
import OptimalG.ContactAnchorAlgebra
import OptimalG.TailControl

/-! Tail control preservation with explicit joining-slope inputs. Negative
state coefficients follow directly from the score and primitive ceilings;
nonnegative coefficients use the two endpoint derivative tests. -/
namespace OptimalG.Variational
open Set MeasureTheory

theorem tailControlSlope_at_join {b Y H lam p theta alpha : ℝ} (hb : b≠1) :
    tailControlSlope (tailBackwardSlope b Y H) (tailBackwardCurvature b Y H)
      lam p theta alpha b=
      -theta+alpha*(b-lam-p+H)-tailOne b Y H/(1-b) := by
  have hs := tailScore_backward b Y H b hb
  rw [tailScore_at_join] at hs
  have hd := tailSlope_backward b Y H b hb
  simp only [tailSlope,tailCoord,sub_self,zero_div,mul_zero,add_zero] at hd
  unfold tailControlSlope
  linear_combination -alpha*hs+hd

theorem Admissible.contact_backwardSlope_gt_five {lam q b Y H : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hq : q∈Icc (0.2635:ℝ) 0.28) (hb : b∈Ioo (0:ℝ) 1)
    (hc : (1-b)^2=2*(lam-q)*capSlack lam d.S q-2*capDeficit lam d.S q)
    (hvalue : Y=b*((1-b)-capSlack lam d.S q))
    (hscore : H=1-2*b-capSlack lam d.S q+b*(1-b)/(lam-q)) :
    5<tailBackwardSlope b Y H := by
  have hL := hd.compact_lambdaRange
  have ha : 0<lam-q := by linarith only [hL.1,hq.2]
  have ha3 : lam-q<(1:ℝ)/3 := by linarith only [hL.2,hq.1]
  have hE := hd.capDeficit_nonneg_before_ell (q:=q) (by
    constructor <;> norm_num [pLo,ell] <;> linarith only [hq.1,hq.2])
  have hh := contact_backward_slope ha.ne' (sub_pos.mpr hb.2).ne' hc
  have he : 1-(1-b)=b := by ring
  rw [he] at hh
  have hs : -1+2*(1-b)-capSlack lam d.S q+b*(1-b)/(lam-q)=H := by
    rw [hscore]
    ring
  rw [hs,←hvalue] at hh
  have heNonneg : 0≤(6-4*(1-b))*capDeficit lam d.S q/((lam-q)*(1-b)^2) :=
    div_nonneg (mul_nonneg (by linarith only [hb.1]) hE)
      (mul_nonneg ha.le (sq_nonneg _))
  have hrecip : (3:ℝ)<1/(lam-q) := (lt_div_iff₀ ha).mpr (by linarith only [ha3])
  linarith only [hh,heNonneg,hrecip]

theorem Admissible.terminal_control_slope_end_pos {lam q b Y H : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S≤(0.023354:ℝ))
    (hq : q∈Icc (0.2635:ℝ) 0.28) (hb : b∈Ioo (0:ℝ) 1)
    (hc : (1-b)^2=2*(lam-q)*capSlack lam d.S q-2*capDeficit lam d.S q)
    (hvalue : Y=b*((1-b)-capSlack lam d.S q))
    (hscore : H=1-2*b-capSlack lam d.S q+b*(1-b)/(lam-q))
    {v : ControlFeature} (hv : v∈controlFeatureSupport d) :
    0<tailControlSlope (tailBackwardSlope b Y H) (tailBackwardCurvature b Y H)
      lam v.1.1 (featureTheta lam d v) (featureAlpha lam d v) 1 := by
  have hv5 := hd.contact_backwardSlope_gt_five hq hb hc hvalue hscore
  have ht := hd.featureTheta_lt_78 hS hv
  have ha := hd.featureAlpha_lt_453 hv
  have hp := (hd.controlFeatureSupport_subset hv).1.1
  have hL := hd.compact_lambdaRange
  norm_num [pLo,pHi] at hp
  have hm := mul_le_mul_of_nonneg_right ha.le
    (show 0≤v.1.1+lam by linarith only [hp.1,hL.1])
  simp only [tailControlSlope,sub_self,mul_zero,zero_pow (by decide : 2≠0),
    add_zero,sub_zero]
  linarith only [hv5,ht,hm,hp.2,hL.2]

theorem tailPrimitive_le_quadratic {lam S b Y H : ℝ} (hb : b<1)
    (h1 : tailOne b Y H≤b-1) (h2 : tailTwo b Y H≤0) (hH : H≤lam-b)
    (hY : Y≤quadratic lam b-S) :
    ∀ r∈Icc b 1,tailPrimitive b Y H r≤quadratic lam r-S := by
  intro r hr
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hr.1
    ((tailScore_continuous b Y H).intervalIntegrable b r)
    ((by fun_prop : Continuous (fun t : ℝ => lam-t)).intervalIntegrable b r)
    (fun t ht => tailScore_ceiling hb h1 h2 hH t ⟨ht.1,ht.2.trans hr.2⟩)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => tailPrimitive_hasDerivAt b Y H t hb.ne)
    ((tailScore_continuous b Y H).intervalIntegrable b r),
    tailPrimitive_at_join,integral_line] at hi
  linarith only [hi,hY]

theorem Admissible.tail_controls_of_contact_slope {lam q b Y H : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S∈Icc (0.02271790:ℝ) 0.023354)
    (hq : q∈Icc (0.2635:ℝ) 0.28) (hb : b∈Ioo zTest 1)
    (hline : H≤lam-b) (hY : Y≤quadratic lam b-d.S)
    (hstart : ∀ v∈controlFeatureSupport d,H≤featureH hd b Y v)
    (hc : (1-b)^2=2*(lam-q)*capSlack lam d.S q-2*capDeficit lam d.S q)
    (hvalue : Y=b*((1-b)-capSlack lam d.S q))
    (hscore : H=1-2*b-capSlack lam d.S q+b*(1-b)/(lam-q))
    (hshape : tailOne b Y H≤b-1 ∧ tailTwo b Y H≤0 ∧
      ∀ v∈controlFeatureSupport d,tailOne b Y H/(1-b)≤
        -featureTheta lam d v+featureAlpha lam d v*(b-lam-v.1.1+H)) :
    ∀ r∈Icc b 1,∀ v∈controlFeatureSupport d,
      tailScore b Y H r≤featureH hd r (tailPrimitive b Y H r) v := by
  have hb01 : b∈Ioo (0:ℝ) 1 :=
    ⟨(by norm_num [zTest] : (0:ℝ)<zTest).trans hb.1,hb.2⟩
  have hprimitive := tailPrimitive_le_quadratic hb.2 hshape.1 hshape.2.1 hline hY
  have hcurv : 0≤tailBackwardCurvature b Y H :=
    div_nonneg (neg_nonneg.mpr hshape.2.1) (sq_nonneg _)
  intro r hr v hv
  rw [featureH_as_highAffineControl hd hv (tailPrimitive b Y H) r]
  by_cases ha : 0≤featureAlpha lam d v
  · apply tailControl_preserved b Y H lam d.S v.1.1 (featureTheta lam d v)
      (featureAlpha lam d v) hb.2 hcurv ha _ _
      (hd.terminal_control_slope_end_pos hS.2 hq hb01 hc hvalue hscore hv).le r hr
    · have hh := hstart v hv
      rw [featureH_as_highAffineControl hd hv (fun _ => Y) b] at hh
      simpa only [tailControlGap,highAffineControl,tailScore_at_join,tailPrimitive_at_join]
        using sub_nonneg.mpr hh
    · rw [tailControlSlope_at_join hb.2.ne]
      exact sub_nonneg.mpr (hshape.2.2 v hv)
  · have hp := (hd.controlFeatureSupport_subset hv).1.1
    have ht := (hd.featureTheta_bounds hv).2.le
    have hL := hd.compact_lambdaRange
    norm_num [pLo,pHi] at hp
    have hrL : lam≤r := by norm_num [zTest] at hb; linarith only [hb.1,hr.1,hL.2]
    have hfactor : 0≤r-lam-v.1.1/2 := by
      norm_num [zTest] at hb
      linarith only [hb.1,hr.1,hL.2,hp.2]
    have hproduct := mul_nonneg (show 0≤v.1.1 by linarith only [hp.1]) hfactor
    have hK : 0≤quadratic lam (r-v.1.1)-d.S-tailPrimitive b Y H r := by
      have hh := hprimitive r hr
      unfold quadratic at hh ⊢
      nlinarith only [hh,hproduct]
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) hK
    have hh := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hrL)
    have hs := tailScore_ceiling hb.2 hshape.1 hshape.2.1 hline r hr
    unfold highAffineControl
    linarith only [hm,hh,hs]

end OptimalG.Variational
