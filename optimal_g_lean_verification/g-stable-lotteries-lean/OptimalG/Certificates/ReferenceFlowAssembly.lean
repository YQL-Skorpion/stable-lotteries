import OptimalG.Certificates.ReferenceCurveLink
import OptimalG.Certificates.ReferenceFlowPartition
import OptimalG.Certificates.ReferenceFlowComparison
import OptimalG.VariationalAffineSolution

/-! The finite time partition, actual local formulas, and C¹ curve checks
construct and enclose an actual reference ODE solution. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

/-- Endpoints of time cells are harmless for the Lebesgue-a.e. hypotheses of
an absolutely continuous affine equation. -/
theorem ae_Icc_of_forall_Ioc {a b : ℝ} {P : ℝ→Prop}
    (h : ∀ t∈Ioc a b,P t) : ∀ᵐ t ∂volume.restrict (Icc a b),P t := by
  filter_upwards [self_mem_ae_restrict measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne a)] with t ht hne
  exact h t ⟨lt_of_le_of_ne ht.1 hne.symm,ht.2⟩

theorem reference_curve_residual {a b L S : ℚ}
    {cells : List ReferenceFlowCell} {pieces : List CubicPiece}
    (pieceFor : ReferenceFlowCell→CubicPiece)
    (hcover : referenceFlowCoverCheck a b cells=true)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpolynomial : ∀ c∈cells,polynomialPieceCheck c.valuePolynomial
      c.segment.left.z c.segment.right.z (pieceFor c)=true)
    (hlookup : ∀ c∈cells,cubicLookupCheck (pieceFor c) pieces=true)
    {eta : ℝ}
    (hresidual : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,
      |c.valuePolynomial.derivative.eval t/(c.length:ℝ)-
        c.actualAlpha t*c.valuePolynomial.eval t-c.actualBeta t|≤eta) :
    ∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),
      |cubicScore L pieces z-referenceField ReferenceFlowCell.actualAlpha cells z*
        cubicPrimitive L S pieces z-referenceField ReferenceFlowCell.actualBeta cells z|≤eta := by
  have hscore := trajectoryCheck_continuousScore L S pieces hcurve
  have hprimitive : Continuous (cubicPrimitive L S pieces) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (trajectoryCheck_hasDerivAt L S pieces hcurve z).continuousAt)
  apply ae_Icc_of_forall_Ioc
  intro z hz
  obtain ⟨c,hmem,hpos,hz',hAlpha⟩ :=
    referenceField_selected ReferenceFlowCell.actualAlpha hcover hz
  have hv := polynomialPieceCheck_global (hpolynomial c hmem) hpos
    (hlookup c hmem) hscore hprimitive ⟨hz'.1.le,hz'.2⟩
  rw [hAlpha,referenceField_on_cell ReferenceFlowCell.actualBeta hcover hmem hz',
    ←hv.1,←hv.2]
  simpa only [ReferenceFlowCell.timeParameter,ReferenceFlowCell.length,Rat.cast_sub] using
    hresidual c hmem _ (c.timeParameter_mem hpos ⟨hz'.1.le,hz'.2⟩)

/-- No numerical ODE solution is assumed: the conclusion uses the actual
integrating-factor solution, whose existence and AC equation are proved. -/
theorem reference_flow_exists_enclosed {a b L S : ℚ}
    {cells : List ReferenceFlowCell} {pieces : List CubicPiece}
    (pieceFor : ReferenceFlowCell→CubicPiece)
    (hcover : referenceFlowCoverCheck a b cells=true)
    (hlen : (b:ℝ)-a≤2/25)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpolynomial : ∀ c∈cells,polynomialPieceCheck c.valuePolynomial
      c.segment.left.z c.segment.right.z (pieceFor c)=true)
    (hlookup : ∀ c∈cells,cubicLookupCheck (pieceFor c) pieces=true)
    (halpha : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,|c.actualAlpha t|≤3)
    (hbeta : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,|c.actualBeta t|≤1000)
    (hresidual : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,
      |c.valuePolynomial.derivative.eval t/(c.length:ℝ)-
        c.actualAlpha t*c.valuePolynomial.eval t-c.actualBeta t|≤1/4000000000) :
    ∃ Z : ℝ→ℝ,
      Z a=cubicPrimitive L S pieces a ∧
      AbsolutelyContinuousOnInterval Z a b ∧
      (∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),deriv Z z=
        referenceField ReferenceFlowCell.actualAlpha cells z*Z z+
          referenceField ReferenceFlowCell.actualBeta cells z) ∧
      ∀ z∈Icc (a:ℝ) b,|Z z-cubicPrimitive L S pieces z|≤(z-a)/2500000000 := by
  have hab := referenceFlowCoverCheck_order hcover
  have hab' : (a:ℝ)≤b := by exact_mod_cast hab
  have ha := referenceField_intervalIntegrable ReferenceFlowCell.actualAlpha hab hcover
    ReferenceFlowCell.actualAlpha_measurable halpha
  have hb := referenceField_intervalIntegrable ReferenceFlowCell.actualBeta hab hcover
    ReferenceFlowCell.actualBeta_measurable hbeta
  obtain ⟨Z,hinit,hAC,hder⟩ := Variational.exists_affine_reference_solution
    (x0:=cubicPrimitive L S pieces a) ha hb
  have hder' : ∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),deriv Z z=
      referenceField ReferenceFlowCell.actualAlpha cells z*Z z+
        referenceField ReferenceFlowCell.actualBeta cells z := by
    filter_upwards [ae_restrict_of_ae hder,self_mem_ae_restrict measurableSet_Icc] with z hd hz
    exact (hd (by simpa only [uIcc_of_le hab'] using hz)).deriv
  have hAlpha : ∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),
      referenceField ReferenceFlowCell.actualAlpha cells z≤3 := by
    apply ae_Icc_of_forall_Ioc
    intro z hz
    exact (le_abs_self _).trans (referenceField_bounded
      ReferenceFlowCell.actualAlpha hcover halpha hz)
  refine ⟨Z,hinit,hAC,hder',?_⟩
  exact reference_flow_enclosed hlen ha (trajectoryCheck_hasDerivAt L S pieces hcurve)
    (trajectoryCheck_continuousScore L S pieces hcurve) hAC hinit.symm hder' hAlpha
    (reference_curve_residual pieceFor hcover hcurve hpolynomial hlookup hresidual)

end OptimalG.Certificates.Transport
