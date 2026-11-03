import OptimalG.Certificates.TerminalShapeData
import OptimalG.VariationalTerminalCoefficients
import OptimalG.VariationalContactTailConsequences

/-! The terminal polynomial tests are applied to the actual contact equation.
The interval variable h=1-z is bounded by two polynomial square tests; the
joining and tail slope numerators are then affine in h. -/
namespace OptimalG.Variational
open Set Certificates.TerminalShape

private theorem affine_positive_from_endpoints {f : ℝ → ℝ} {a b x : ℝ}
    (hab : a<b) (hx : x∈Icc a b)
    (hid : (b-a)*f x=(b-x)*f a+(x-a)*f b)
    (ha : 0<f a) (hb : 0<f b) : 0<f x := by
  have hleft := mul_nonneg (sub_nonneg.mpr hx.2) ha.le
  have hright := mul_nonneg (sub_nonneg.mpr hx.1) hb.le
  have hsum : 0<(b-x)*f a+(x-a)*f b := by
    rcases lt_or_eq_of_le hx.1 with hax | hax
    · have hp := mul_pos (sub_pos.mpr hax) hb
      linarith only [hleft,hp]
    · subst x
      simpa only [sub_self,zero_mul,add_zero] using mul_pos (sub_pos.mpr hab) ha
  exact pos_of_mul_pos_right (hid.symm ▸ hsum) (sub_nonneg.mpr hab.le)

private theorem contact_height_bounds {lam S q h h0 h1 : ℝ}
    (hh : 0≤h) (hq : q<1) (hzero : 0≤h0) (hone : 0≤h1)
    (hc : h^2=2*(lam-q)*capSlack lam S q-2*capDeficit lam S q)
    (hlower : 0<contactNumerator lam S q-h0^2*denominator q)
    (hupper : 0<h1^2*denominator q-contactNumerator lam S q) :
    h∈Icc h0 h1 := by
  have hD : 0<denominator q := sq_pos_of_pos (sub_pos.mpr hq)
  have hid : contactNumerator lam S q=h^2*denominator q := by
    rw [contactNumerator_eq lam S q hq.ne,←hc]
  rw [hid] at hlower hupper
  have hlo : h0^2<h^2 := (mul_lt_mul_iff_left₀ hD).mp (by nlinarith only [hlower])
  have hup : h^2<h1^2 := (mul_lt_mul_iff_left₀ hD).mp (by nlinarith only [hupper])
  constructor <;> nlinarith only [hlo,hup,hh,hzero,hone]

theorem terminal_contact_numerators_positive {lam S q h : ℝ}
    (hL : lam∈Icc (0.562325:ℝ) 0.562330)
    (hS : S∈Icc (0.02271790:ℝ) 0.023354)
    (hq : q∈Icc (0.2635:ℝ) 0.28) (hh : 0≤h)
    (hc : h^2=2*(lam-q)*capSlack lam S q-2*capDeficit lam S q) :
    0<joinNumerator lam S q h ∧ 0<tailNumerator lam S q h := by
  have hq1 : q<1 := by linarith only [hq.2]
  by_cases hcut : q≤(0.272:ℝ)
  · have hq0 : q∈Icc (0.2635:ℝ) 0.272 := ⟨hq.1,hcut⟩
    have hheight := contact_height_bounds hh hq1 (by norm_num : (0:ℝ)≤0.1335)
      (by norm_num : (0:ℝ)≤0.1505) hc
      (Certificates.TerminalShapeData.Box0SquareLower.positive hL hS hq0)
      (Certificates.TerminalShapeData.Box0SquareUpper.positive hL hS hq0)
    exact ⟨affine_positive_from_endpoints (by norm_num) hheight
      (joinNumerator_affine lam S q h 0.1335 0.1505)
      (Certificates.TerminalShapeData.Box0JoinLower.positive hL hS hq0)
      (Certificates.TerminalShapeData.Box0JoinUpper.positive hL hS hq0),
      affine_positive_from_endpoints (by norm_num) hheight
      (tailNumerator_affine lam S q h 0.1335 0.1505)
      (Certificates.TerminalShapeData.Box0TailLower.positive hL hS hq0)
      (Certificates.TerminalShapeData.Box0TailUpper.positive hL hS hq0)⟩
  · have hq1' : q∈Icc (0.272:ℝ) 0.28 := ⟨(lt_of_not_ge hcut).le,hq.2⟩
    have hheight := contact_height_bounds hh hq1 (by norm_num : (0:ℝ)≤0.1165)
      (by norm_num : (0:ℝ)≤0.134) hc
      (Certificates.TerminalShapeData.Box1SquareLower.positive hL hS hq1')
      (Certificates.TerminalShapeData.Box1SquareUpper.positive hL hS hq1')
    exact ⟨affine_positive_from_endpoints (by norm_num) hheight
      (joinNumerator_affine lam S q h 0.1165 0.134)
      (Certificates.TerminalShapeData.Box1JoinLower.positive hL hS hq1')
      (Certificates.TerminalShapeData.Box1JoinUpper.positive hL hS hq1'),
      affine_positive_from_endpoints (by norm_num) hheight
      (tailNumerator_affine lam S q h 0.1165 0.134)
      (Certificates.TerminalShapeData.Box1TailLower.positive hL hS hq1')
      (Certificates.TerminalShapeData.Box1TailUpper.positive hL hS hq1')⟩

theorem terminal_contact_tail_slope {lam S q b Y H : ℝ}
    (hL : lam∈Icc (0.562325:ℝ) 0.562330)
    (hS : S∈Icc (0.02271790:ℝ) 0.023354)
    (hq : q∈Icc (0.2635:ℝ) 0.28) (hb : b<1)
    (hc : (1-b)^2=2*(lam-q)*capSlack lam S q-2*capDeficit lam S q)
    (hvalue : Y=b*((1-b)-capSlack lam S q))
    (hscore : H=1-2*b-capSlack lam S q+b*(1-b)/(lam-q)) :
    tailOne b Y H/(1-b)< -1 ∧
      tailOne b Y H/(1-b)< -0.78+4.53*(H+b-lam-0.36) := by
  have ha : 0<lam-q := by linarith only [hL.1,hq.2]
  have hh : 0<1-b := sub_pos.mpr hb
  have hq1 : q≠1 := by linarith only [hq.2]
  have hn := terminal_contact_numerators_positive hL hS hq hh.le hc
  have hpos : 0<(lam-q)*(1-b)^2*(denominator q)^2 := by
    have hD : 0<denominator q := sq_pos_of_pos (by linarith only [hq.2] : 0<1-q)
    positivity
  rw [joinNumerator_contact_identity ha.ne' hh.ne' hq1 hc] at hn
  rw [tailNumerator_contact_identity ha.ne' hh.ne' hq1 hc] at hn
  have he : 1-(1-b)=b := by ring
  have hs : -1+2*(1-b)-capSlack lam S q+b*(1-b)/(lam-q)=H := by rw [hscore];ring
  rw [he,hs,←hvalue] at hn
  have htail := (mul_pos_iff_of_pos_right hpos).mp (by simpa only [mul_assoc] using hn.2)
  have hjoin := (mul_pos_iff_of_pos_right hpos).mp (by simpa only [mul_assoc] using hn.1)
  constructor <;> linarith only [htail,hjoin]

theorem Admissible.terminal_contact_shape {lam q b Y H : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S∈Icc (0.02271790:ℝ) 0.023354)
    (hq : q∈Icc (0.2635:ℝ) 0.28) (hb : b∈Ioo (0:ℝ) 1)
    (hline : H≤lam-b)
    (hc : (1-b)^2=2*(lam-q)*capSlack lam d.S q-2*capDeficit lam d.S q)
    (hvalue : Y=b*((1-b)-capSlack lam d.S q))
    (hscore : H=1-2*b-capSlack lam d.S q+b*(1-b)/(lam-q)) :
    tailOne b Y H≤b-1 ∧ tailTwo b Y H≤0 ∧
      ∀ v∈controlFeatureSupport d,tailOne b Y H/(1-b)≤
        -featureTheta lam d v+featureAlpha lam d v*(b-lam-v.1.1+H) := by
  have ht := terminal_contact_tail_slope hd.compact_lambdaRange hS hq hb.2 hc hvalue hscore
  have hq' : q∈Icc pLo ell := by
    constructor <;> norm_num [pLo,ell] <;> linarith only [hq.1,hq.2]
  refine ⟨?_,hd.tailTwo_nonpos_of_contact hq' hb hc hvalue hscore,?_⟩
  · have hm := (div_le_iff₀ (sub_pos.mpr hb.2)).mp ht.1.le
    linarith only [hm]
  · intro v hv
    exact ht.2.le.trans (terminal_control_slope_lower hd hS.2 hv hline)

theorem completedVariationalScore_concave_of_terminal_contact {lam a b q : ℝ}
    {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : 0<a) (hax : a≤xHi) (hb : b∈Ioo zStart zEnd)
    (hS : d.S∈Icc (0.02271790:ℝ) 0.023354)
    (hq : q∈Icc (0.2635:ℝ) 0.28)
    (hxjoin : low xHi=lam-xHi)
    (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hactive : ∀ r∈Icc zStart b,∀ v∈controlFeatureSupport d,
      featureH hd r (Y r) v=vectorField lam d r (Y r) →
      vectorField lam d r (Y r)≠lam-r →
      1≤featureTheta lam d v+featureAlpha lam d v*v.1.1)
    (hc : (1-b)^2=2*(lam-q)*capSlack lam d.S q-2*capDeficit lam d.S q)
    (hvalue : Y b=b*((1-b)-capSlack lam d.S q))
    (hscore : continuationScore lam d Y b=
      1-2*b-capSlack lam d.S q+b*(1-b)/(lam-q)) :
    ConcaveOn ℝ (Icc lam 1) (completedVariationalScore a lam d low Y b) := by
  have hb' : b∈Ioo (0:ℝ) 1 := by
    constructor <;> norm_num [zStart,zEnd] at hb <;> linarith only [hb.1,hb.2]
  have hshape := hd.terminal_contact_shape hS hq hb'
    (vectorField_le_line lam d b (Y b)) hc hvalue hscore
  change tailOne b (Y b) (continuationScore lam d Y b)≤b-1 ∧
    tailTwo b (Y b) (continuationScore lam d Y b)≤0 ∧
    (∀ v∈controlFeatureSupport d,tailOne b (Y b) (continuationScore lam d Y b)/(1-b)≤
      -featureTheta lam d v+featureAlpha lam d v*(b-lam-v.1.1+continuationScore lam d Y b)) at hshape
  have hm : tailOne b (Y b) (continuationScore lam d Y b)/(1-b)≤ -1 := by
    apply (div_le_iff₀ (sub_pos.mpr hb'.2)).mpr
    linarith only [hshape.1]
  exact completedVariationalScore_concave_of_active_slope_bounds hd hY ha hax hb
    hxjoin hzjoin hactive hm (fun v hv _ _ => hshape.2.2 v hv) hshape.2.1 le_rfl

end OptimalG.Variational
