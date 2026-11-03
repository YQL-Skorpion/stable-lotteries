import OptimalG.Certificates.ReferenceCurveMembership
import OptimalG.Certificates.ReferenceScalarCertificate

/-! The actual reference solution follows from a finite list of checked
scalar certificates, the time cover, and the C¹ coefficient joins. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

namespace ReferenceFlowCell

def canonicalPiece (c : ReferenceFlowCell) : CubicPiece :=
  ⟨c.segment.left.z,c.segment.right.z,
    c.valuePolynomial[1]?.getD 0/c.length,
    2*c.valuePolynomial[2]?.getD 0/c.length^2,
    3*c.valuePolynomial[3]?.getD 0/c.length^3,
    0,c.valuePolynomial[0]?.getD 0⟩

def canonicalPieceCheck (c : ReferenceFlowCell) : Bool :=
  polynomialPieceCheck c.valuePolynomial c.segment.left.z c.segment.right.z c.canonicalPiece

end ReferenceFlowCell

/-- All premises here are finite Boolean checks apart from the elementary
positive scale and interval-length bounds. The output is a genuine AC ODE
solution, not an interpretation of the supplied cubic as an exact solution. -/
theorem checked_reference_flow_exists {a b L S : ℚ} {scale : ℕ}
    (hscale : 0<scale) (certificates : List ReferenceScalarCertificate)
    (hcert : certificates.all (fun c => c.check scale)=true)
    (hcover : referenceFlowCoverCheck a b (certificates.map (fun c => c.cell.flow))=true)
    (hcurve : trajectoryCheck L S
      (certificates.map (fun c => c.cell.flow.canonicalPiece))=true)
    (hpoly : certificates.all (fun c => c.cell.flow.canonicalPieceCheck)=true)
    (hlen : (b:ℝ)-a≤2/25) :
    ∃ Z : ℝ→ℝ,
      Z a=cubicPrimitive L S (certificates.map (fun c => c.cell.flow.canonicalPiece)) a ∧
      AbsolutelyContinuousOnInterval Z a b ∧
      (∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),deriv Z z=
        referenceField ReferenceFlowCell.actualAlpha (certificates.map (fun c => c.cell.flow)) z*Z z+
          referenceField ReferenceFlowCell.actualBeta (certificates.map (fun c => c.cell.flow)) z) ∧
      ∀ z∈Icc (a:ℝ) b,
        |Z z-cubicPrimitive L S (certificates.map (fun c => c.cell.flow.canonicalPiece)) z|
          ≤(z-a)/2500000000 := by
  have hb (c : ReferenceScalarCertificate) (hc : c∈certificates) (t : ℝ)
      (ht : t∈Icc (0:ℝ) 1) := c.checked_bounds hscale (List.all_eq_true.mp hcert c hc) ht
  apply reference_flow_exists_enclosed_of_membership ReferenceFlowCell.canonicalPiece hcover hlen hcurve
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact List.all_eq_true.mp hpoly d hd
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  · intro c hc t ht
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact (hb d hd t ht).2.2.1
  · intro c hc t ht
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact (hb d hd t ht).2.2.2.1
  · intro c hc t ht
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    apply (hb d hd t ht).1.trans
    have hn : (scale/4000000000)*4000000000≤scale := Nat.div_mul_le_self scale 4000000000
    have hr : ((scale/4000000000:ℕ):ℝ)*4000000000≤(scale:ℝ) := by exact_mod_cast hn
    apply (div_le_iff₀ (show (0:ℝ)<scale by exact_mod_cast hscale)).mpr
    linarith

end OptimalG.Certificates.Transport
