import OptimalG.VariationalSlopeClassification
import OptimalG.VariationalUniformRightSlope
import OptimalG.VariationalLowCurve

/-! The only exceptional lower-slope obligation is the coupled diagonal.
All non-diagonal active ranks already satisfy the bound from the universally
proved theta < 1. The remaining numerical diagonal bound stays explicit. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped NNReal

 theorem minimizer_lower_increment_of_diagonal {lam c : ℝ} {d : LowRankData}
    {psi : ℝ → ℝ} {L : ℝ≥0}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ico xLo xHi)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r=cap lam d.S r → r ≤ c)
    (hpsi : LipschitzWith L psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (hprimitive : ∀ r ∈ Icc c xHi, lowPrimitive lam d r=cap lam d.S c+∫ t in c..r,psi t)
    (hdiag : ∀ r ∈ Ioo c xHi, ∀ z ∈ Icc zStart zEnd, ∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v=vectorField lam d z (continuation lam d z) →
      v.1.1=r → v.1.2.2=r → v.1.2.1 ≤ r → r ∈ Ioo pLo pHi →
      -1 ≤ diagonalFeatureSlope lam d z (continuation lam d z) v r (psi r)) :
    ∀ r ∈ Icc c xHi, ∀ s ∈ Icc c xHi, r ≤ s → psi r-(s-r) ≤ psi s := by
  have hclass := minimizer_slope_classification hd hl hmin hpass hc hlast hpsi heq hprimitive
  have hder : ∀ᵐ r ∂volume.restrict (Icc c xHi), deriv (fun t => -psi t) r ≤ 1 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo,hclass] with r hr hh
    have hneg := hh.1.neg
    change HasDerivAt (fun t => -psi t) (-deriv psi r) r at hneg
    rw [hneg.deriv]
    rcases hh.2 with hline | ⟨z,hz,v,hv,hactive,hcases⟩
    · rw [hline]
      norm_num
    · rcases hcases with htheta | ⟨hp,hy,hx,hpRange,hslope⟩
      · rw [htheta]
        linarith [(hd.featureTheta_bounds hv).2]
      · rw [hslope]
        linarith [hdiag r hr z hz v hv hactive hp hy hx hpRange]
  intro r hr s hs hrs
  have hi := lipschitz_increment_le_of_deriv_le_ae hpsi.neg.lipschitzOnWith hder hr hs hrs
  change -psi s-(-psi r) ≤ 1*(s-r) at hi
  linarith

 theorem minimizer_strictAnti_of_theta {lam c theta : ℝ} {d : LowRankData}
    {psi : ℝ → ℝ} {L : ℝ≥0}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ico xLo xHi)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r=cap lam d.S r → r ≤ c)
    (hpsi : LipschitzWith L psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hactiveTheta : ∀ z ∈ Icc zStart zEnd, ∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v=vectorField lam d z (continuation lam d z) →
      theta ≤ featureTheta lam d v) :
    StrictAntiOn psi (Icc c xHi) := by
  have hi := minimizer_uniform_right_slope hd hl hmin hpass hc hlast hpsi.continuous heq htheta1 hactiveTheta
  intro r hr s hs hrs
  have hh := hi r hr s hs hrs.le
  have hp := mul_pos htheta (sub_pos.mpr hrs)
  linarith

 theorem Admissible.capScore_slope_ge_neg_one {lam r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hr : r ≤ xHi) : -1 ≤ -2*lam*d.S/(1-r)^3 := by
  have hL := hd.compact_lambdaRange
  have hS := hd.slack_upper
  have hS0 : 0 ≤ d.S := by linarith [hd.slack_lower]
  have hr' : r ≤ (0.38 : ℝ) := by convert! hr using 1 <;> norm_num [xHi]
  have hnum := mul_le_mul hL.2 hS hS0 (by norm_num : (0:ℝ) ≤ 0.562330)
  have hpow : (0.62 : ℝ)^3 ≤ (1-r)^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1-r) 3)).mpr
  nlinarith only [hnum,hpow]

 theorem minimizer_capRegularScore_shape {lam c a theta : ℝ} {d : LowRankData}
    {psi : ℝ → ℝ} {L : ℝ≥0}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ioo xLo xHi) (ha : a ≤ ell)
    (hcap : ∀ r ∈ Icc ell c, lowPrimitive lam d r=cap lam d.S r)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r=cap lam d.S r → r ≤ c)
    (hpsi : LipschitzWith L psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (hpos : ∀ r ∈ Icc c xHi, 0 < psi r ∧ psi r ≤ lam-r)
    (hprimitive : ∀ r ∈ Icc c xHi, lowPrimitive lam d r=cap lam d.S c+∫ t in c..r,psi t)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hactiveTheta : ∀ z ∈ Icc zStart zEnd, ∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v=vectorField lam d z (continuation lam d z) →
      theta ≤ featureTheta lam d v)
    (hdiag : ∀ r ∈ Ioo c xHi, ∀ z ∈ Icc zStart zEnd, ∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v=vectorField lam d z (continuation lam d z) →
      v.1.1=r → v.1.2.2=r → v.1.2.1 ≤ r → r ∈ Ioo pLo pHi →
      -1 ≤ diagonalFeatureSlope lam d z (continuation lam d z) v r (psi r)) :
    Continuous (capRegularScore lam d.S c psi) ∧
      StrictAntiOn (capRegularScore lam d.S c psi) (Icc a xHi) ∧
      LipschitzOnWith 1 (capRegularScore lam d.S c psi) (Icc a xHi) ∧
      (∀ r ∈ Icc a xHi, 0 < capRegularScore lam d.S c psi r ∧
        capRegularScore lam d.S c psi r ≤ lam-r) ∧
      (∀ r ∈ Icc a xHi, primitive lam d r=cap lam d.S a+∫ t in a..r,capRegularScore lam d.S c psi t) ∧
      d.phi =ᵐ[volume.restrict (Icc xLo xHi)] capRegularScore lam d.S c psi := by
  have hci : c ∈ Ico xLo xHi := ⟨hc.1.le,hc.2⟩
  have hce : ell < c := (by norm_num [ell,xLo] : ell < xLo).trans hc.1
  have hct : c ≤ tEnd := hc.2.le.trans (by norm_num [xHi,tEnd])
  have hac : a ≤ c := ha.trans hce.le
  have hjoin := minimizer_score_continuous_at_contact hd hl hmin hpass hc hcap hlast
    hpsi.continuous heq hprimitive
  have hlo := minimizer_lower_increment_of_diagonal hd hl hmin hpass hci hlast hpsi heq hprimitive hdiag
  have hm := minimizer_strictAnti_of_theta hd hl hmin hpass hci hlast hpsi heq htheta htheta1 hactiveTheta
  have hscoreM := capRegularScore_strictAntiOn hac hc.2.le (by norm_num [xHi])
    (by have hh := hd.1.1; norm_num [lambdaLo] at hh;linarith)
    (by linarith [hd.slack_lower]) hjoin hm
  have hscoreLo := capRegularScore_lower_increment hac hc.2.le (by norm_num [xHi]) hjoin
    (fun r hr => hd.capScore_slope_ge_neg_one (hr.2.trans hc.2.le)) hlo
  refine ⟨capRegularScore_continuous (hc.2.trans (by norm_num [xHi])) hpsi.continuous hjoin,
    hscoreM,antitone_lower_increment_lipschitz hscoreM.antitoneOn hscoreLo,
    capRegularScore_bounds hd ⟨hce,hct⟩ (hcap c ⟨hce.le,le_rfl⟩) hpos,
    capRegularScore_primitive hac ⟨hce.le,hc.2.le⟩ hpsi.continuous hjoin hcap hprimitive,
    hd.capRegularScore_ae ⟨hc.1.le,hc.2.le⟩ hcap heq⟩

end OptimalG.Variational
