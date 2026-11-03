import OptimalG.EnvelopeFlowComparison
import OptimalG.RawControlSupport

/-! The signed-to-admissible envelope bridge with the raw-control hypothesis
fully discharged by continuity and the positive determinant gap. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem raw_envelope_vectorField_le {lam delta z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {J phi : ℝ → ℝ} {K : ℝ≥0}
    (hJ : LipschitzWith K J) (hphi : ContinuousOn phi (Icc xLo xHi))
    (hdelta : 0 < delta) (hdet : ∀ v ∈ controlDomain, delta ≤ rawDet lam J v)
    (hselect : ∀ᵐ r ∂volume.restrict (Icc ell xHi), d.phi r = 0 ∨ d.phi r = phi r)
    (hmid : ∀ r ∈ Icc xHi zStart, J r = quadratic lam r-d.S)
    (hR : ∀ p ∈ Icc pLo pHi, J p ≤ primitive lam d p)
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S) :
    rawVectorField lam J phi z u ≤ vectorField lam d z u := by
  apply raw_envelope_vectorField_comparison hd hphi hselect hmid hR
    (fun v hv => hdelta.trans_le (hdet v hv)) _ hz huLow huHigh
  exact fun v hv => rawVectorField_le_control hJ hphi hdelta hdet z u v hv

theorem raw_envelope_continuation_le {lam delta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {J phi X : ℝ → ℝ} {K : ℝ≥0}
    (hJ : LipschitzWith K J) (hphi : ContinuousOn phi (Icc xLo xHi))
    (hdelta : 0 < delta) (hdet : ∀ v ∈ controlDomain, delta ≤ rawDet lam J v)
    (hselect : ∀ᵐ r ∂volume.restrict (Icc ell xHi), d.phi r = 0 ∨ d.phi r = phi r)
    (hmid : ∀ r ∈ Icc xHi zStart, J r = quadratic lam r-d.S)
    (hR : ∀ p ∈ Icc pLo pHi, J p ≤ primitive lam d p)
    (hX : ContinuousOn X (Icc zStart zEnd))
    (hXd : ∀ z ∈ Ico zStart zEnd, HasDerivWithinAt X (rawVectorField lam J phi z (X z)) (Ici z) z)
    (hXlo : ∀ z ∈ Icc zStart zEnd, quadratic lam z-quadratic lam 1 ≤ X z)
    (hXhi : ∀ z ∈ Icc zStart zEnd, X z ≤ quadratic lam z-d.S)
    (hXinit : X zStart ≤ quadratic lam zStart-d.S) :
    ∀ z ∈ Icc zStart zEnd, X z ≤ continuation lam d z := by
  apply raw_envelope_continuation_comparison hd hphi hselect hmid hR
    (fun v hv => hdelta.trans_le (hdet v hv)) _ hX hXd hXlo hXhi hXinit
  exact fun z _ v hv => rawVectorField_le_control hJ hphi hdelta hdet z (X z) v hv

/-- Concrete B.1 conclusion from the signed pre-envelope trajectory and the
actual admissible envelope data. -/
theorem feasible_of_raw_envelope {lam delta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {J phi X : ℝ → ℝ} {K : ℝ≥0}
    (hJ : LipschitzWith K J) (hphi : ContinuousOn phi (Icc xLo xHi))
    (hdelta : 0 < delta) (hdet : ∀ v ∈ controlDomain, delta ≤ rawDet lam J v)
    (hselect : ∀ᵐ r ∂volume.restrict (Icc ell xHi), d.phi r = 0 ∨ d.phi r = phi r)
    (hmid : ∀ r ∈ Icc xHi zStart, J r = quadratic lam r-d.S)
    (hR : ∀ p ∈ Icc pLo pHi, J p ≤ primitive lam d p)
    (hcap : ∀ q ∈ Icc qLo qHi, J q ≤ cap lam d.S q)
    (hX : ContinuousOn X (Icc zStart zEnd))
    (hXd : ∀ z ∈ Ico zStart zEnd, HasDerivWithinAt X (rawVectorField lam J phi z (X z)) (Ici z) z)
    (hXlo : ∀ z ∈ Icc zStart zEnd, quadratic lam z-quadratic lam 1 ≤ X z)
    (hXhi : ∀ z ∈ Icc zStart zEnd, X z ≤ quadratic lam z-d.S)
    (hXinit : X zStart ≤ quadratic lam zStart-d.S)
    (htests : ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      z*(J (1-z+q)-J q)/(lam-q) ≤ X z) : Feasible lam := by
  have hcompare := raw_envelope_continuation_le hd hJ hphi hdelta hdet hselect hmid hR hX hXd hXlo hXhi hXinit
  exact ⟨d,hd,continuation lam d,hd.isContinuation,raw_envelope_passesTerminalTests hd hmid hcap htests hcompare⟩

end OptimalG.Variational
