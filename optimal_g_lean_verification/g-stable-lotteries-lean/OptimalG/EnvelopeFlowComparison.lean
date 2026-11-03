import OptimalG.EnvelopeGraphRelation
import OptimalG.SignedRationalControl

/-! The B.1 running-envelope comparison with the actual signed raw field.
The only pointwise envelope hypothesis here is the raw-control lower-bound
property, to be supplied from continuity of the original controls. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

private theorem raw_middle_arguments {z : ℝ} {v : Control}
    (hv : v ∈ controlDomain) (hz : z ∈ Icc zStart zEnd) :
    1-v.1 ∈ Icc xHi zStart ∧ z-v.1 ∈ Icc xHi zStart := by
  have hp := hv.1
  norm_num [pLo,pHi] at hp
  norm_num [zStart,zEnd] at hz
  norm_num [xHi,zStart]
  exact ⟨⟨by linarith [hp.2],by linarith [hp.1]⟩,
    ⟨by linarith [hp.2,hz.1],by linarith [hp.1,hz.2]⟩⟩

theorem raw_envelope_feature_comparison {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {J phi : ℝ → ℝ}
    (hphi : ContinuousOn phi (Icc xLo xHi))
    (hselect : ∀ᵐ r ∂volume.restrict (Icc ell xHi), d.phi r = 0 ∨ d.phi r = phi r)
    (hmid : ∀ r ∈ Icc xHi zStart, J r = quadratic lam r-d.S)
    (hR : ∀ p ∈ Icc pLo pHi, J p ≤ primitive lam d p)
    (hdet : ∀ v ∈ controlDomain, 0 < rawDet lam J v)
    (hlower : ∀ v ∈ controlDomain, rawVectorField lam J phi z u ≤
      signedControlH lam J (rawAlpha lam J phi) (rawBeta lam J phi) (·.1) z u v)
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d) :
    rawVectorField lam J phi z u ≤ featureH hd z u v := by
  have hline : rawVectorField lam J phi z u ≤ lam-z := min_le_left _ _
  by_cases hactive : featureH hd z u v ≤ lam-z
  · obtain ⟨w,hw,hp,hwA,hwB,hwv⟩ := select_original_envelope_feature hd hphi hselect hz huLow huHigh hv
    have hwdom := (hd.controlFeatureSupport_subset hw).1
    have hwx := hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hw).1
    have hwy := hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hw).2
    have ha := hd.feature_alpha_positive hwdom hz huLow huHigh hwx.2.2 hwy.2.2 (hwv.trans hactive)
    have hcy := (hd.control_coefficients_positive hwdom hz huLow huHigh).2
    have hargs := raw_middle_arguments hwdom hz
    have hP := hmid (1-w.1.1) hargs.1
    have hK := hmid (z-w.1.1) hargs.2
    have hD : 0 < Certificates.Control.det (2*lam-w.1.2.1) (w.1.1+w.1.2.2-lam)
        (primitive lam d w.1.1) (quadratic lam (1-w.1.1)-d.S) := by
      change 0 < controlDeterminant lam d w.1
      linarith [hd.determinant_positive hwdom]
    have hD' : 0 < Certificates.Control.det (2*lam-w.1.2.1) (w.1.1+w.1.2.2-lam)
        (J w.1.1) (quadratic lam (1-w.1.1)-d.S) := by
      have hh := hdet w.1 hwdom
      unfold rawDet at hh
      rw [hP] at hh
      exact hh
    have hvalue := Certificates.Control.value_R_decrease_nonincreasing (z-lam) (2*lam-w.1.2.1)
      (w.1.1+w.1.2.2-lam) (primitive lam d w.1.1) (J w.1.1)
      (quadratic lam (1-w.1.1)-d.S) (quadratic lam (z-w.1.1)-d.S-u)
      w.2.1 w.2.2 hD hD' (hR w.1.1 hwdom.1) ha.le (by linarith)
    have hraw : signedControlH lam J (rawAlpha lam J phi) (rawBeta lam J phi) (·.1) z u w.1 ≤
        featureH hd z u w := by
      rw [rawControl_eq_value,featureH_eq_value hd z u w.2.1 w.2.2 hwdom,hP,hK,← hwA,← hwB]
      exact hvalue
    exact (hlower w.1 hwdom).trans (hraw.trans hwv)
  · exact hline.trans (le_of_not_ge hactive)

/-- The post-envelope variational vector field dominates the actual signed
pre-envelope field at every state between the root budget and the ceiling. -/
theorem raw_envelope_vectorField_comparison {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {J phi : ℝ → ℝ}
    (hphi : ContinuousOn phi (Icc xLo xHi))
    (hselect : ∀ᵐ r ∂volume.restrict (Icc ell xHi), d.phi r = 0 ∨ d.phi r = phi r)
    (hmid : ∀ r ∈ Icc xHi zStart, J r = quadratic lam r-d.S)
    (hR : ∀ p ∈ Icc pLo pHi, J p ≤ primitive lam d p)
    (hdet : ∀ v ∈ controlDomain, 0 < rawDet lam J v)
    (hlower : ∀ v ∈ controlDomain, rawVectorField lam J phi z u ≤
      signedControlH lam J (rawAlpha lam J phi) (rawBeta lam J phi) (·.1) z u v)
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S) :
    rawVectorField lam J phi z u ≤ vectorField lam d z u := by
  apply le_min (min_le_left _ _)
  obtain ⟨v,hv,heq⟩ := hd.essInf_attained_in_featureSupport z u
  rw [← heq]
  exact raw_envelope_feature_comparison hd hphi hselect hmid hR hdet hlower hz huLow huHigh hv

/-- The complete scalar comparison for an actual pre-envelope trajectory. -/
theorem raw_envelope_continuation_comparison {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {J phi X : ℝ → ℝ}
    (hphi : ContinuousOn phi (Icc xLo xHi))
    (hselect : ∀ᵐ r ∂volume.restrict (Icc ell xHi), d.phi r = 0 ∨ d.phi r = phi r)
    (hmid : ∀ r ∈ Icc xHi zStart, J r = quadratic lam r-d.S)
    (hR : ∀ p ∈ Icc pLo pHi, J p ≤ primitive lam d p)
    (hdet : ∀ v ∈ controlDomain, 0 < rawDet lam J v)
    (hlower : ∀ z ∈ Icc zStart zEnd, ∀ v ∈ controlDomain,
      rawVectorField lam J phi z (X z) ≤
      signedControlH lam J (rawAlpha lam J phi) (rawBeta lam J phi) (·.1) z (X z) v)
    (hX : ContinuousOn X (Icc zStart zEnd))
    (hXd : ∀ z ∈ Ico zStart zEnd, HasDerivWithinAt X (rawVectorField lam J phi z (X z)) (Ici z) z)
    (hXlo : ∀ z ∈ Icc zStart zEnd, quadratic lam z-quadratic lam 1 ≤ X z)
    (hXhi : ∀ z ∈ Icc zStart zEnd, X z ≤ quadratic lam z-d.S)
    (hXinit : X zStart ≤ quadratic lam zStart-d.S) :
    ∀ z ∈ Icc zStart zEnd, X z ≤ continuation lam d z := by
  apply scalar_ode_comparison (vectorField lam d) (19/2) X (continuation lam d)
    (fun z => rawVectorField lam J phi z (X z)) (fun z => vectorField lam d z (continuation lam d z))
    zStart zEnd (fun z _ => hd.vectorField_lipschitz z) hX (continuation_continuous hd.isContinuation)
    hXd (fun z hz => hd.isContinuation.right_derivative hz) _ (fun _ _ => le_rfl)
  · rwa [hd.isContinuation.1]
  · intro z hz
    have hz' : z ∈ Icc zStart zEnd := ⟨hz.1,hz.2.le⟩
    exact raw_envelope_vectorField_comparison hd hphi hselect hmid hR hdet (hlower z hz') hz' (hXlo z hz') (hXhi z hz')

/-- Raising the low terminal rank to the cap decreases the two-class obstacle. -/
theorem raw_envelope_terminal_comparison {lam z q : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {J : ℝ → ℝ}
    (hmid : ∀ r ∈ Icc xHi zStart, J r = quadratic lam r-d.S)
    (hcap : ∀ r ∈ Icc qLo qHi, J r ≤ cap lam d.S r)
    (hz : z ∈ Icc zTest zEnd) (hq : q ∈ Icc qLo qHi) :
    terminalBound lam d.S z q ≤ z*(J (1-z+q)-J q)/(lam-q) := by
  have hl := hd.1.1
  have hz' := hz
  have hq' := hq
  norm_num [lambdaLo,zTest,zEnd,qLo,qHi] at hl hz' hq'
  have harg : 1-z+q ∈ Icc xHi zStart := by
    norm_num [xHi,zStart]
    exact ⟨by linarith [hz'.2,hq'.1],by linarith [hz'.1,hq'.2]⟩
  have hJ := hmid (1-z+q) harg
  have hJq := hcap q hq
  have hnum : quadratic lam (1-z+q)-d.S-cap lam d.S q ≤ J (1-z+q)-J q := by
    rw [hJ]
    linarith
  unfold terminalBound
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by linarith [hz'.1])) (by linarith [hq'.2])

theorem raw_envelope_passesTerminalTests {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {J X : ℝ → ℝ}
    (hmid : ∀ r ∈ Icc xHi zStart, J r = quadratic lam r-d.S)
    (hcap : ∀ r ∈ Icc qLo qHi, J r ≤ cap lam d.S r)
    (hraw : ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      z*(J (1-z+q)-J q)/(lam-q) ≤ X z)
    (hcompare : ∀ z ∈ Icc zStart zEnd, X z ≤ continuation lam d z) :
    PassesTerminalTests lam d (continuation lam d) := by
  intro z hz q hq
  exact (raw_envelope_terminal_comparison hd hmid hcap hz hq).trans
    ((hraw z hz q hq).trans (hcompare z ⟨(by norm_num [zStart,zTest] : zStart ≤ zTest).trans hz.1,hz.2⟩))

end OptimalG.Variational
