import OptimalG.VariationalTerminalShape
import OptimalG.VariationalTailControlBounds
import OptimalG.PrimitiveBounds

/-! Every essential-support control survives the completed tail. Positive
state coefficients use the two endpoint derivative tests; negative state
coefficients follow directly from the score and primitive ceilings. -/
namespace OptimalG.Variational
open Set MeasureTheory

theorem Admissible.terminal_tail_controls {lam q b Y H : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S∈Icc (0.02271790:ℝ) 0.023354)
    (hq : q∈Icc (0.2635:ℝ) 0.28) (hb : b∈Ioo zTest 1)
    (hline : H≤lam-b) (hY : Y≤quadratic lam b-d.S)
    (hstart : ∀ v∈controlFeatureSupport d,H≤featureH hd b Y v)
    (hc : (1-b)^2=2*(lam-q)*capSlack lam d.S q-2*capDeficit lam d.S q)
    (hvalue : Y=b*((1-b)-capSlack lam d.S q))
    (hscore : H=1-2*b-capSlack lam d.S q+b*(1-b)/(lam-q)) :
    ∀ r∈Icc b 1,∀ v∈controlFeatureSupport d,
      tailScore b Y H r≤featureH hd r (tailPrimitive b Y H r) v := by
  have hb01 : b∈Ioo (0:ℝ) 1 :=
    ⟨(by norm_num [zTest] : (0:ℝ)<zTest).trans hb.1,hb.2⟩
  exact hd.tail_controls_of_contact_slope hS hq hb hline hY hstart hc hvalue hscore
    (hd.terminal_contact_shape hS hq hb01 hline hc hvalue hscore)

theorem completedVariationalScore_controls_of_terminal_contact {lam a b q : ℝ}
    {d : LowRankData} {low : ℝ → ℝ}
    (hd : Admissible lam d) (ha : 0<a) (hax : a≤xHi)
    (hb : b∈Ioo zTest zEnd) (hS : d.S∈Icc (0.02271790:ℝ) 0.023354)
    (hq : q∈Icc (0.2635:ℝ) 0.28)
    (hxjoin : low xHi=lam-xHi)
    (hzjoin : continuationScore lam d (continuation lam d) zStart=lam-zStart)
    (hcurve : VerifierCurve (completedVariationalScore a lam d low (continuation lam d) b) lam)
    (hprim : ∀ r∈Icc zStart b,
      curvePrimitive (completedVariationalScore a lam d low (continuation lam d) b) r=
        continuation lam d r)
    (hc : (1-b)^2=2*(lam-q)*capSlack lam d.S q-2*capDeficit lam d.S q)
    (hvalue : continuation lam d b=b*((1-b)-capSlack lam d.S q))
    (hscore : continuationScore lam d (continuation lam d) b=
      1-2*b-capSlack lam d.S q+b*(1-b)/(lam-q)) :
    ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport d,
      completedVariationalScore a lam d low (continuation lam d) b r≤
        featureH hd r
          (curvePrimitive (completedVariationalScore a lam d low (continuation lam d) b) r) v := by
  let phi := completedVariationalScore a lam d low (continuation lam d) b
  let H := continuationScore lam d (continuation lam d) b
  let Y := continuation lam d b
  have hxz : xHi≤zStart := by norm_num [xHi,zStart]
  have hzb : zStart≤b := (by norm_num [zStart,zTest] : zStart≤zTest).trans hb.1.le
  have hb1 : b<1 := hb.2.trans (by norm_num [zEnd])
  have hb0 : 0≤b := (by norm_num [zStart] : (0:ℝ)≤zStart).trans hzb
  have htailScore : ∀ r,b≤r → phi r=tailScore b Y H r := by
    intro r hr
    exact completedScore_tail ha.ne' (hax.trans (hxz.trans hzb))
      (middleScore_low _ _ _ _ hax) (middleScore_high hxjoin hzjoin hzb) hr
  have htailPrim : ∀ r∈Icc b 1,curvePrimitive phi r=tailPrimitive b Y H r := by
    intro r hr
    have hi : (∫ t in b..r,phi t)=tailPrimitive b Y H r-Y := by
      calc
        _ = ∫ t in b..r,tailScore b Y H t := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hr.1] at ht
          exact htailScore t ht.1
        _ = _ := by
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun t _ => tailPrimitive_hasDerivAt b Y H t hb1.ne)
            ((tailScore_continuous b Y H).intervalIntegrable b r),tailPrimitive_at_join]
    rw [←hcurve.primitive_difference hb0 hr.1 hr.2,hprim b ⟨hzb,le_rfl⟩] at hi
    change curvePrimitive phi r-Y=tailPrimitive b Y H r-Y at hi
    linarith only [hi]
  have hstart : ∀ v∈controlFeatureSupport d,H≤featureH hd b Y v := by
    intro v hv
    exact (min_le_right _ _).trans (hd.essInf_le_featureH b Y hv)
  have htail := hd.terminal_tail_controls hS hq ⟨hb.1,hb1⟩
    (vectorField_le_line lam d b Y)
    (hd.continuation_le_quadratic hd.isContinuation b ⟨hzb,hb.2.le⟩)
    hstart hc hvalue hscore
  intro r hr v hv
  by_cases hrb : r≤b
  · rw [hprim r ⟨hr.1,hrb⟩]
    have hphi : phi r=continuationScore lam d (continuation lam d) r := by
      dsimp only [phi,completedVariationalScore]
      rw [completedScore_middle ha.ne'
        (hax.trans (hxz.trans hzb)) (middleScore_low _ _ _ _ hax)
        ⟨hax.trans (hxz.trans hr.1),hrb⟩,middleScore_high hxjoin hzjoin hr.1]
    rw [show completedVariationalScore a lam d low (continuation lam d) b r=
      continuationScore lam d (continuation lam d) r from hphi]
    exact (min_le_right _ _).trans (hd.essInf_le_featureH r (continuation lam d r) hv)
  · change phi r≤featureH hd r (curvePrimitive phi r) v
    rw [htailScore r (le_of_not_ge hrb),htailPrim r ⟨le_of_not_ge hrb,hr.2⟩]
    exact htail r ⟨le_of_not_ge hrb,hr.2⟩ v hv

end OptimalG.Variational
