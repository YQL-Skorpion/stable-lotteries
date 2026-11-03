import OptimalG.Certificates.ReferenceCheckedFlow
import OptimalG.Certificates.ReferenceScalarTolerance
import OptimalG.Certificates.HighPieceCover

/-! Adjustable residual tolerances enclose a genuine affine reference solution.
The original fine-mesh checker and bounds remain unchanged. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem reference_flow_enclosed_with_tolerance {a b epsilon : ℝ}
    {alpha beta X X' Z : ℝ→ℝ}
    (heps : 0≤epsilon) (hlen : b-a≤2/25)
    (ha : IntervalIntegrable alpha volume a b)
    (hXder : ∀ t,HasDerivAt X (X' t) t) (hXcont : Continuous X')
    (hZ : AbsolutelyContinuousOnInterval Z a b) (hinit : X a=Z a)
    (hZd : ∀ᵐ t ∂volume.restrict (Icc a b),deriv Z t=alpha t*Z t+beta t)
    (hAlpha : ∀ᵐ t ∂volume.restrict (Icc a b),alpha t≤3)
    (hResidual : ∀ᵐ t ∂volume.restrict (Icc a b),
      |X' t-alpha t*X t-beta t|≤epsilon) :
    ∀ t∈Icc a b,|Z t-X t|≤2*epsilon*(t-a) := by
  apply affine_flow_enclosed_by_residual (A:=3) (delta:=2*epsilon)
    (by norm_num) (by positivity) ?_ ha hXder hXcont hZ hinit hZd hAlpha hResidual
  have hm := mul_nonneg heps (show 0≤(2:ℝ)/25-(b-a) by linarith)
  nlinarith

theorem reference_flow_exists_enclosed_with_tolerance {a b L S : ℚ} {epsilon : ℝ}
    {cells : List ReferenceFlowCell} {pieces : List CubicPiece}
    (pieceFor : ReferenceFlowCell→CubicPiece)
    (hcover : referenceFlowCoverCheck a b cells=true)
    (hlen : (b:ℝ)-a≤2/25) (heps : 0≤epsilon)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpolynomial : ∀ c∈cells,polynomialPieceCheck c.valuePolynomial
      c.segment.left.z c.segment.right.z (pieceFor c)=true)
    (hlookup : ∀ c∈cells,cubicLookupCheck (pieceFor c) pieces=true)
    (halpha : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,|c.actualAlpha t|≤3)
    (hbeta : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,|c.actualBeta t|≤1000)
    (hresidual : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,
      |c.valuePolynomial.derivative.eval t/(c.length:ℝ)-
        c.actualAlpha t*c.valuePolynomial.eval t-c.actualBeta t|≤epsilon) :
    ∃ Z : ℝ→ℝ,
      Z a=cubicPrimitive L S pieces a ∧
      AbsolutelyContinuousOnInterval Z a b ∧
      (∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),deriv Z z=
        referenceField ReferenceFlowCell.actualAlpha cells z*Z z+
          referenceField ReferenceFlowCell.actualBeta cells z) ∧
      ∀ z∈Icc (a:ℝ) b,|Z z-cubicPrimitive L S pieces z|≤2*epsilon*(z-a) := by
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
  exact reference_flow_enclosed_with_tolerance heps hlen ha (trajectoryCheck_hasDerivAt L S pieces hcurve)
    (trajectoryCheck_continuousScore L S pieces hcurve) hAC hinit.symm hder' hAlpha
    (reference_curve_residual pieceFor hcover hcurve hpolynomial hlookup hresidual)


theorem checked_reference_flow_exists_with_tolerance {a b L S : ℚ} {scale : ℕ}
    {residual : ℤ} {epsilon : ℝ}
    (hscale : 0<scale) (certificates : List ReferenceScalarCertificate)
    (hcert : certificates.all (fun c => c.checkWithTolerance scale residual)=true)
    (hcover : referenceFlowCoverCheck a b (certificates.map (fun c => c.cell.flow))=true)
    (hcurve : trajectoryCheck L S
      (certificates.map (fun c => c.cell.flow.canonicalPiece))=true)
    (hpoly : certificates.all (fun c => c.cell.flow.canonicalPieceCheck)=true)
    (hlen : (b:ℝ)-a≤2/25) (heps : 0≤epsilon)
    (hresidual : (residual:ℝ)/(scale:ℝ)≤epsilon) :
    ∃ Z : ℝ→ℝ,
      Z a=cubicPrimitive L S (certificates.map (fun c => c.cell.flow.canonicalPiece)) a ∧
      AbsolutelyContinuousOnInterval Z a b ∧
      (∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),deriv Z z=
        referenceField ReferenceFlowCell.actualAlpha (certificates.map (fun c => c.cell.flow)) z*Z z+
          referenceField ReferenceFlowCell.actualBeta (certificates.map (fun c => c.cell.flow)) z) ∧
      ∀ z∈Icc (a:ℝ) b,
        |Z z-cubicPrimitive L S (certificates.map (fun c => c.cell.flow.canonicalPiece)) z|
          ≤2*epsilon*(z-a) := by
  have hb (c : ReferenceScalarCertificate) (hc : c∈certificates) (t : ℝ)
      (ht : t∈Icc (0:ℝ) 1) := c.checked_bounds_with_tolerance hscale (List.all_eq_true.mp hcert c hc) ht
  apply reference_flow_exists_enclosed_with_tolerance ReferenceFlowCell.canonicalPiece hcover hlen heps hcurve
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact List.all_eq_true.mp hpoly d hd
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact HighPieceCover.member_lookup hcurve (List.mem_map.mpr ⟨d,hd,rfl⟩)
  · intro c hc t ht
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact (hb d hd t ht).2.2.1
  · intro c hc t ht
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact (hb d hd t ht).2.2.2.1
  · intro c hc t ht
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact (hb d hd t ht).1.trans hresidual

end OptimalG.Certificates.Transport
