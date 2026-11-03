import OptimalG.VariationalSlackSlope
import OptimalG.VariationalLowCurve

/-! The positive-slack slope bounds imply that the recovered minimizing
score actually reaches the line before the last control rank. -/
namespace OptimalG.Variational
open Set MeasureTheory
open scoped NNReal

 theorem scoreSlack_lipschitz {lam : ℝ} {psi : ℝ → ℝ} {L : ℝ≥0}
    (hpsi : LipschitzWith L psi) : LipschitzWith (1+L) (scoreSlack lam psi) := by
  apply LipschitzWith.of_dist_le_mul
  intro r s
  rw [Real.dist_eq,Real.dist_eq]
  change |lam-r-psi r-(lam-s-psi s)| ≤ (1+(L:ℝ))*|r-s|
  calc
    _ = |(s-r)+(psi s-psi r)| := by congr 1; ring
    _ ≤ |s-r|+|psi s-psi r| := abs_add_le _ _
    _ ≤ |s-r|+(L:ℝ)*|s-r| := add_le_add le_rfl
      (by simpa only [Real.dist_eq] using hpsi.dist_le_mul s r)
    _ = _ := by rw [abs_sub_comm s r];ring

 theorem minimizer_line_at_xHi {lam c a C gamma : ℝ} {d : LowRankData}
    {psi : ℝ → ℝ} {L : ℝ≥0}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ico xLo xHi) (ha : a ∈ Icc c xHi)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r=cap lam d.S r → r ≤ c)
    (hpsi : LipschitzWith L psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (hprimitive : ∀ r ∈ Icc c xHi,lowPrimitive lam d r=cap lam d.S c+∫ t in c..r,psi t)
    (hceiling : ∀ r ∈ Icc c xHi,psi r ≤ lam-r)
    (hstart : scoreSlack lam psi a < C) (hgamma : 0 ≤ gamma)
    (htime : C ≤ gamma*(xHi-a))
    (htheta : ∀ z ∈ Icc zStart zEnd,∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v=vectorField lam d z (continuation lam d z) →
      featureTheta lam d v ≤ 1-gamma)
    (hdiag : ∀ z ∈ Icc zStart zEnd,∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v=vectorField lam d z (continuation lam d z) →
      ∀ r ∈ Ioo a xHi,r ∈ Ioo pLo pHi → v.1.1=r → v.1.2.2=r → v.1.2.1 ≤ r →
      0 < scoreSlack lam psi r → scoreSlack lam psi r ≤ C →
      -1+gamma ≤ diagonalFeatureSlope lam d z (continuation lam d z) v r (psi r)) :
    psi xHi=lam-xHi := by
  have hpos : ∀ r ∈ Icc a xHi,0 ≤ scoreSlack lam psi r := by
    intro r hr
    exact sub_nonneg.mpr (hceiling r ⟨ha.1.trans hr.1,hr.2⟩)
  have hder := minimizer_slack_derivative_bound hd hl hmin hpass hc ha.1 le_rfl hlast hpsi heq
    hprimitive htheta hdiag
  have hh := (lipschitz_nonnegative_band_decay (scoreSlack_lipschitz hpsi) hstart hgamma hpos hder).2.2
    xHi ⟨ha.2,le_rfl⟩
  rw [max_eq_left (by linarith : scoreSlack lam psi a-gamma*(xHi-a) ≤ 0)] at hh
  have hzero := le_antisymm hh (hpos xHi ⟨ha.2,le_rfl⟩)
  unfold scoreSlack at hzero
  linarith

 theorem minimizer_line_after {lam c a t C gamma : ℝ} {d : LowRankData}
    {psi : ℝ → ℝ} {L : ℝ≥0}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ico xLo xHi) (ha : a ∈ Icc c xHi)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r=cap lam d.S r → r ≤ c)
    (hpsi : LipschitzWith L psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (hprimitive : ∀ r ∈ Icc c xHi,lowPrimitive lam d r=cap lam d.S c+∫ t in c..r,psi t)
    (hceiling : ∀ r ∈ Icc c xHi,psi r ≤ lam-r)
    (hstart : scoreSlack lam psi a < C) (hgamma : 0 ≤ gamma)
    (ht : t ∈ Icc a xHi) (htime : C ≤ gamma*(t-a))
    (htheta : ∀ z ∈ Icc zStart zEnd,∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v=vectorField lam d z (continuation lam d z) →
      featureTheta lam d v ≤ 1-gamma)
    (hdiag : ∀ z ∈ Icc zStart zEnd,∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v=vectorField lam d z (continuation lam d z) →
      ∀ r ∈ Ioo a xHi,r ∈ Ioo pLo pHi → v.1.1=r → v.1.2.2=r → v.1.2.1 ≤ r →
      0 < scoreSlack lam psi r → scoreSlack lam psi r ≤ C →
      -1+gamma ≤ diagonalFeatureSlope lam d z (continuation lam d z) v r (psi r)) :
    ∀ r ∈ Icc t xHi,psi r=lam-r := by
  have hpos : ∀ r ∈ Icc a xHi,0 ≤ scoreSlack lam psi r := by
    intro r hr
    exact sub_nonneg.mpr (hceiling r ⟨ha.1.trans hr.1,hr.2⟩)
  have hder := minimizer_slack_derivative_bound hd hl hmin hpass hc ha.1 le_rfl hlast hpsi heq
    hprimitive htheta hdiag
  intro r hr
  have har : a ≤ r := ht.1.trans hr.1
  have htimeR : C ≤ gamma*(r-a) := htime.trans
    (mul_le_mul_of_nonneg_left (by linarith [hr.1] : t-a ≤ r-a) hgamma)
  have hh := (lipschitz_nonnegative_band_decay (scoreSlack_lipschitz hpsi) hstart hgamma hpos hder).2.2
    r ⟨har,hr.2⟩
  rw [max_eq_left (by linarith : scoreSlack lam psi a-gamma*(r-a) ≤ 0)] at hh
  have hzero := le_antisymm hh (hpos r ⟨har,hr.2⟩)
  unfold scoreSlack at hzero
  linarith

end OptimalG.Variational
