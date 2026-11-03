import OptimalG.VariationalSlopeClassification
import OptimalG.VariationalSlackBand

/-! The exact active-rank alternatives imply the scalar slack differential
inequality once the explicit numerical support and diagonal bounds hold. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

noncomputable def scoreSlack (lam : ℝ) (psi : ℝ → ℝ) (r : ℝ) : ℝ := lam-r-psi r

 theorem minimizer_slack_derivative_bound {lam c a b C gamma : ℝ} {d : LowRankData}
    {psi : ℝ → ℝ} {L : ℝ≥0}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ico xLo xHi) (ha : c ≤ a) (hb : b ≤ xHi)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c)
    (hpsi : LipschitzWith L psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (hprimitive : ∀ r ∈ Icc c xHi, lowPrimitive lam d r = cap lam d.S c+∫ t in c..r, psi t)
    (htheta : ∀ z ∈ Icc zStart zEnd, ∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v = vectorField lam d z (continuation lam d z) →
      featureTheta lam d v ≤ 1-gamma)
    (hdiag : ∀ z ∈ Icc zStart zEnd, ∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v = vectorField lam d z (continuation lam d z) →
      ∀ r ∈ Ioo a b, r ∈ Ioo pLo pHi → v.1.1=r → v.1.2.2=r → v.1.2.1 ≤ r →
      0 < scoreSlack lam psi r → scoreSlack lam psi r ≤ C →
      -1+gamma ≤ diagonalFeatureSlope lam d z (continuation lam d z) v r (psi r)) :
    ∀ᵐ r ∂volume.restrict (Icc a b),
      0 < scoreSlack lam psi r → scoreSlack lam psi r ≤ C →
        deriv (scoreSlack lam psi) r ≤ -gamma := by
  have hsub : Ioo a b ⊆ Ioo c xHi := Ioo_subset_Ioo ha hb
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset hsub
      (minimizer_slope_classification_strong hd hl hmin hpass hc hlast hpsi heq hprimitive)]
    with r hr hclass hp hb
  have hder : HasDerivAt (scoreSlack lam psi) (-1-deriv psi r) r := by
    convert! ((hasDerivAt_const r lam).sub (hasDerivAt_id r)).sub hclass.1 using 1 <;>
      simp [scoreSlack]
  rw [hder.deriv]
  rcases hclass.2 with hsat | ⟨z,hz,v,hv,hactive,hcase⟩
  · exfalso
    simpa [scoreSlack,hsat.1] using hp
  · rcases hcase with hline | ⟨hpr,hyr,hxr,hrp,hdiageq⟩
    · have hh := htheta z hz v hv hactive
      rw [hline]
      linarith
    · have hh := hdiag z hz v hv hactive r hr hrp hpr hyr hxr hp hb
      rw [hdiageq]
      linarith

end OptimalG.Variational
