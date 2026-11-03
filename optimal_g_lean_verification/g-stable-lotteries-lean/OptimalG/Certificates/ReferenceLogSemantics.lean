import OptimalG.Certificates.ReferenceAdjointWeights
import OptimalG.VariationalReferenceTerms

/-! The checked reference coefficients generate the logarithm of the actual
reference affine solution. Their delta-weighted sum is exactly beta/Z, so the
adjoint already used by the finite weight certificates is the integrating
factor in the transport inequality. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory Real Variational

namespace ReferenceFlowCell

theorem baseCoefficientExpr_transport (c : ReferenceFlowCell) (i : Fin 4) (t : ℝ) :
    (c.baseCoefficientExpr i).evalOne t=
      if c.late then lateLogCoefficients c.lam c.level c.slack
        (c.highRank.evalOne t) (c.rankR.evalOne t) (c.rankA.evalOne t)
        (localPrimitive c.lam c.slack c.rPiece (c.rankR.evalOne t)) 1
        (localScore c.lam c.slack c.rPiece (c.rankR.evalOne t))
        (localScore c.lam c.slack c.aPiece (c.rankA.evalOne t)) i
      else earlyLogCoefficients c.lam c.level c.slack
        (c.highRank.evalOne t) (c.rankR.evalOne t) (c.rankA.evalOne t)
        (localPrimitive c.lam c.slack c.rPiece (c.rankR.evalOne t)) 1
        (localScore c.lam c.slack c.aPiece (c.rankA.evalOne t)) i := by
  rw [baseCoefficientExpr_eval,FrozenParameters.coefficients_eval]
  simp [baseInput,baseSubstitution,frozenParameters,FrozenParameters.referenceHighRank,
    FrozenParameters.referencePrimitive,FrozenParameters.jacobian,
    FrozenParameters.shiftedScoreR,FrozenParameters.shiftedScoreA,
    Rexpr,scoreR,scoreA,primitiveExpr_eval,scoreExpr_eval,RatExpr.evalOne,RatExpr.eval]

theorem base_reference_sum (c : ReferenceFlowCell) (t Z : ℝ) (hZ : 0<Z) :
    (∑ i,referenceWeight ((c.baseCoefficientExpr i).evalOne t) (transportDelta i) (log Z))=
      c.actualAlpha t+c.actualBeta t/Z := by
  simp_rw [baseCoefficientExpr_transport]
  cases hb : c.late
  · simpa only [hb,Bool.false_eq_true,↓reduceIte,actualAlpha,actualBeta] using
      early_reference_sum c.lam c.level c.slack (c.highRank.evalOne t)
        (c.rankR.evalOne t) (c.rankA.evalOne t)
        (localPrimitive c.lam c.slack c.rPiece (c.rankR.evalOne t))
        (localScore c.lam c.slack c.aPiece (c.rankA.evalOne t)) Z hZ
  · simpa only [hb,↓reduceIte,actualAlpha,actualBeta] using
      late_reference_sum c.lam c.level c.slack (c.highRank.evalOne t)
        (c.rankR.evalOne t) (c.rankA.evalOne t)
        (localPrimitive c.lam c.slack c.rPiece (c.rankR.evalOne t))
        (localScore c.lam c.slack c.rPiece (c.rankR.evalOne t))
        (localScore c.lam c.slack c.aPiece (c.rankA.evalOne t)) Z hZ

theorem base_reference_B (c : ReferenceFlowCell) (t Z : ℝ) (hZ : 0<Z) :
    (∑ i,transportDelta i*referenceWeight ((c.baseCoefficientExpr i).evalOne t)
      (transportDelta i) (log Z))=c.actualBeta t/Z := by
  simp_rw [baseCoefficientExpr_transport]
  cases hb : c.late
  · simpa only [hb,Bool.false_eq_true,↓reduceIte,actualBeta] using
      early_reference_B c.lam c.level c.slack (c.highRank.evalOne t)
        (c.rankR.evalOne t) (c.rankA.evalOne t)
        (localPrimitive c.lam c.slack c.rPiece (c.rankR.evalOne t))
        (localScore c.lam c.slack c.aPiece (c.rankA.evalOne t)) Z hZ
  · simpa only [hb,↓reduceIte,actualBeta] using
      late_reference_B c.lam c.level c.slack (c.highRank.evalOne t)
        (c.rankR.evalOne t) (c.rankA.evalOne t)
        (localPrimitive c.lam c.slack c.rPiece (c.rankR.evalOne t))
        (localScore c.lam c.slack c.rPiece (c.rankR.evalOne t))
        (localScore c.lam c.slack c.aPiece (c.rankA.evalOne t)) Z hZ

end ReferenceFlowCell

theorem referenceCoefficient_sum_and_B {start finish : ℚ}
    {cells : List ReferenceFlowCell} (hc : referenceFlowCoverCheck start finish cells=true)
    {z Z : ℝ} (hz : z∈Ioc (start:ℝ) finish) (hZ : 0<Z) :
    (∑ i,referenceWeight (referenceCoefficient cells i z) (transportDelta i) (log Z))=
      referenceField ReferenceFlowCell.actualAlpha cells z+
        referenceField ReferenceFlowCell.actualBeta cells z/Z ∧
    (∑ i,transportDelta i*referenceWeight (referenceCoefficient cells i z)
      (transportDelta i) (log Z))=referenceField ReferenceFlowCell.actualBeta cells z/Z := by
  obtain ⟨c,hmem,_,hzi,_⟩ := referenceField_selected ReferenceFlowCell.actualAlpha hc hz
  have he (i : Fin 4) : referenceCoefficient cells i z=
      (c.baseCoefficientExpr i).evalOne (c.timeParameter z) :=
    referenceField_on_cell _ hc hmem hzi
  simp_rw [he,referenceField_on_cell ReferenceFlowCell.actualAlpha hc hmem hzi,
    referenceField_on_cell ReferenceFlowCell.actualBeta hc hmem hzi]
  exact ⟨c.base_reference_sum _ _ hZ,c.base_reference_B _ _ hZ⟩

theorem reference_log_derivative {start finish : ℚ} {cells : List ReferenceFlowCell}
    {Z : ℝ→ℝ} (hc : referenceFlowCoverCheck start finish cells=true)
    (hZ : AbsolutelyContinuousOnInterval Z start finish)
    (hpos : ∀ z∈Icc (start:ℝ) finish,0<Z z)
    (hder : ∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),
      deriv Z z=referenceField ReferenceFlowCell.actualAlpha cells z*Z z+
        referenceField ReferenceFlowCell.actualBeta cells z) :
    AbsolutelyContinuousOnInterval (fun z=>log (Z z)) start finish ∧
    (∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),
      deriv (fun z=>log (Z z)) z=
        ∑ i,referenceWeight (referenceCoefficient cells i z) (transportDelta i) (log (Z z))) := by
  have hab : (start:ℝ)≤finish := by exact_mod_cast referenceFlowCoverCheck_order hc
  refine ⟨absolutelyContinuous_log hZ (by simpa only [uIcc_of_le hab] using hpos),?_⟩
  have hdiff : ∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),DifferentiableAt ℝ Z z := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    simpa only [uIcc_of_le hab] using hZ.ae_differentiableAt
  have hmem : ∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),z∈Ioc (start:ℝ) finish := by
    rw [←restrict_Ioc_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioc
  filter_upwards [hder,hdiff,hmem] with z hd hz hzi
  have hp := hpos z ⟨hzi.1.le,hzi.2⟩
  rw [(hz.hasDerivAt.log hp.ne').deriv,hd,
    (referenceCoefficient_sum_and_B hc hzi hp).1]
  field_simp [hp.ne']
  <;> ring

theorem reference_transport_B_integrable {start finish : ℚ} {cells : List ReferenceFlowCell}
    {Z : ℝ→ℝ} (hc : referenceFlowCoverCheck start finish cells=true)
    (hb : IntervalIntegrable (referenceField ReferenceFlowCell.actualBeta cells) volume
      (start:ℝ) finish)
    (hZ : AbsolutelyContinuousOnInterval Z start finish)
    (hpos : ∀ z∈Icc (start:ℝ) finish,0<Z z) :
    IntervalIntegrable (transportReferenceB (fun z i=>referenceCoefficient cells i z)
      transportDelta (fun z=>log (Z z))) volume (start:ℝ) finish := by
  have hab : (start:ℝ)≤finish := by exact_mod_cast referenceFlowCoverCheck_order hc
  have hi : ContinuousOn (fun z=>(Z z)⁻¹) (uIcc (start:ℝ) finish) := by
    apply hZ.continuousOn.inv₀
    intro z hz
    exact (hpos z (by simpa only [uIcc_of_le hab] using hz)).ne'
  have hB : IntervalIntegrable (fun z=>referenceField ReferenceFlowCell.actualBeta cells z/Z z)
      volume (start:ℝ) finish := by
    simpa only [div_eq_mul_inv] using hb.mul_continuousOn hi
  apply hB.congr_uIoo
  rw [uIoo_of_le hab]
  intro z hz
  exact (referenceCoefficient_sum_and_B hc ⟨hz.1,hz.2.le⟩
    (hpos z ⟨hz.1.le,hz.2.le⟩)).2.symm

theorem reference_transport_adjoint {start finish : ℚ} {cells : List ReferenceFlowCell}
    {Z : ℝ→ℝ} (hc : referenceFlowCoverCheck start finish cells=true)
    (hpos : ∀ z∈Icc (start:ℝ) finish,0<Z z) {s : ℝ}
    (hs : s∈Icc (start:ℝ) finish) :
    referenceIntegratingFactor start finish
      (transportReferenceB (fun z i=>referenceCoefficient cells i z) transportDelta
        (fun z=>log (Z z))) s=
      referenceIntegratingFactor start finish
        (fun z=>referenceField ReferenceFlowCell.actualBeta cells z/Z z) s := by
  have hab : (start:ℝ)≤finish := hs.1.trans hs.2
  unfold referenceIntegratingFactor
  congr 2
  · apply intervalIntegral.integral_congr_Ioo_of_le hs.1
    intro z hz
    exact (referenceCoefficient_sum_and_B hc ⟨hz.1,hz.2.le.trans hs.2⟩
      (hpos z ⟨hz.1.le,hz.2.le.trans hs.2⟩)).2
  · apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro z hz
    exact (referenceCoefficient_sum_and_B hc ⟨hz.1,hz.2.le⟩
      (hpos z ⟨hz.1.le,hz.2.le⟩)).2

end OptimalG.Certificates.Transport
