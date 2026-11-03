import OptimalG.Certificates.ReferenceFlowTolerance
import OptimalG.Certificates.ReferenceScalarTolerances

/-! Actual primary flow from independently checked primary/auxiliary residuals. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem checked_reference_flow_exists_with_tolerances {a b L S : ℚ} {scale : ℕ}
    {residual auxiliaryResidual : ℤ} {epsilon : ℝ}
    (hscale : 0<scale) (certificates : List ReferenceScalarCertificate)
    (hcert : certificates.all (fun c => c.checkWithTolerances scale residual auxiliaryResidual)=true)
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
      (ht : t∈Icc (0:ℝ) 1) := c.checked_bounds_with_tolerances hscale (List.all_eq_true.mp hcert c hc) ht
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
