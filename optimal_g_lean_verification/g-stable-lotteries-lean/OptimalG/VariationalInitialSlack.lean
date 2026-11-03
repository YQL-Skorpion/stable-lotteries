import OptimalG.VariationalLowSlope
import OptimalG.VariationalLineContact

/-! The scalar tube and safe cap contact give the initial slack band;
the actual slope classification propagates that band along the minimizer. -/
namespace OptimalG.Variational
open Set MeasureTheory
open scoped NNReal

 theorem Admissible.capSlack_antitone {lam a : ℝ} {d : LowRankData}
    (hd : Admissible lam d) : AntitoneOn (capSlack lam d.S) (Icc a xHi) := by
  have hder (r : ℝ) (hr : r ∈ Icc a xHi) :
      HasDerivAt (capSlack lam d.S) (-1-(-2*lam*d.S/(1-r)^3)) r := by
    have hh := ((hasDerivAt_const r lam).sub (hasDerivAt_id r)).sub
      (capScore_hasDerivAt lam d.S r (ne_of_lt (hr.2.trans_lt (by norm_num [xHi]))))
    convert! hh using 1 <;> simp [capSlack]
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun r hr => (hder r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hder r (interior_subset hr)).differentiableAt.differentiableWithinAt)
  intro r hr
  rw [(hder r (interior_subset hr)).deriv]
  linarith [hd.capScore_slope_ge_neg_one (interior_subset hr).2]

 theorem Admissible.capSlack_lt_initial_band {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S ≤ (0.023354 : ℝ))
    (hc : c ∈ Icc (0.2854 : ℝ) xHi) : capSlack lam d.S c < (0.022 : ℝ) := by
  have hm := hd.capSlack_antitone (a:=0.2854) ⟨le_rfl,hc.1.trans hc.2⟩ hc hc.1
  have hL := hd.compact_lambdaRange
  have hS0 : 0 ≤ d.S := by linarith [hd.slack_lower]
  have hLS := mul_le_mul hL.2 hS hS0 (by norm_num : (0:ℝ) ≤ 0.562330)
  have hbound : capSlack lam d.S (0.2854 : ℝ) < (0.022 : ℝ) := by
    unfold capSlack capScore
    norm_num
    nlinarith only [hL.2,hLS]
  exact hm.trans_lt hbound

 theorem minimizer_slack_stays_below {lam c b C : ℝ} {d : LowRankData}
    {psi : ℝ → ℝ} {L : ℝ≥0}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam',Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ico xLo xHi) (hb : b ≤ xHi)
    (hlast : ∀ r ∈ Icc ell tEnd,lowPrimitive lam d r=cap lam d.S r → r ≤ c)
    (hpsi : LipschitzWith L psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (hprimitive : ∀ r ∈ Icc c xHi,lowPrimitive lam d r=cap lam d.S c+∫ t in c..r,psi t)
    (hceiling : ∀ r ∈ Icc c xHi,psi r ≤ lam-r)
    (hstart : scoreSlack lam psi c < C)
    (hdiag : ∀ z ∈ Icc zStart zEnd,∀ v ∈ controlFeatureSupport d,
      featureH hd z (continuation lam d z) v=vectorField lam d z (continuation lam d z) →
      ∀ r ∈ Ioo c b,r ∈ Ioo pLo pHi → v.1.1=r → v.1.2.2=r → v.1.2.1 ≤ r →
      0 < scoreSlack lam psi r → scoreSlack lam psi r ≤ C →
      -1 ≤ diagonalFeatureSlope lam d z (continuation lam d z) v r (psi r)) :
    ∀ r ∈ Icc c b,scoreSlack lam psi r < C := by
  have hder := minimizer_slack_derivative_bound hd hl hmin hpass hc le_rfl hb hlast hpsi heq hprimitive
    (gamma:=0) (fun z hz v hv ha => by linarith [(hd.featureTheta_bounds hv).2])
    (by simpa only [add_zero] using hdiag)
  apply lipschitz_nonnegative_stays_below
    (scoreSlack_lipschitz hpsi)
    hstart
  · intro r hr
    exact sub_nonneg.mpr (hceiling r ⟨hr.1,hr.2.trans hb⟩)
  · simpa only [neg_zero] using hder

end OptimalG.Variational
