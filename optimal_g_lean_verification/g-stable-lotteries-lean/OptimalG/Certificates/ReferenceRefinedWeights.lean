import OptimalG.Certificates.ReferenceWeightCertificate
import OptimalG.Certificates.ReferenceCheckedFlow
import OptimalG.Certificates.ReferenceRefinementField

/-! The local numerical weight records enclose the actual global reference
field and the actual enclosed affine solution on every refined time cell. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem checked_refined_alpha_mass {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (hc : c.check s k=true)
    {start finish lo hi : ℚ} {cells : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck c.cell.flow lo hi=true) :
    c.mass.Contains s (∫ z in (c.cell.flow.segment.left.z:ℝ)..c.cell.flow.segment.right.z,
      referenceField ReferenceFlowCell.actualAlpha cells z) := by
  rw [referenceField_refined_alpha_integral hcover hmem href]
  exact c.checked_integral hs hk hc

theorem checked_refined_alpha_bound {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (hc : c.check s k=true)
    {start finish lo hi : ℚ} {cells : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck c.cell.flow lo hi=true) :
    ∀ᵐ z ∂volume.restrict (Icc (c.cell.flow.segment.left.z:ℝ) c.cell.flow.segment.right.z),
      c.alphaBounds.Contains s (referenceField ReferenceFlowCell.actualAlpha cells z) := by
  apply ae_Icc_of_forall_Ioc
  intro z hz
  rw [(referenceField_on_refined_cell hcover hmem href hz).1]
  have hpos := (ReferenceFlowCell.refinement_time_geometry href
    (referenceFlowCoverCheck_bounds hcover hmem).2.1).1
  exact c.checked_alpha hs hk hc (c.cell.flow.timeParameter_mem hpos ⟨hz.1.le,hz.2⟩)

theorem refined_polynomial_global {start finish lo hi L S : ℚ}
    {cells : List ReferenceFlowCell} {parent child : ReferenceFlowCell}
    {pieces : List CubicPiece}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck child lo hi=true)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpiece : parent.canonicalPiece∈pieces) (hpoly : parent.canonicalPieceCheck=true)
    {z : ℝ} (hz : z∈Icc (child.segment.left.z:ℝ) child.segment.right.z) :
    child.valuePolynomial.eval (child.timeParameter z)=cubicPrimitive L S pieces z := by
  have hparent := referenceFlowCoverCheck_bounds hcover hmem
  have hg := ReferenceFlowCell.refinement_time_geometry href hparent.2.1
  have hzp : z∈Icc (parent.segment.left.z:ℝ) parent.segment.right.z :=
    ⟨(show (parent.segment.left.z:ℝ)≤child.segment.left.z by exact_mod_cast hg.2.1).trans hz.1,
      hz.2.trans (by exact_mod_cast hg.2.2.1)⟩
  have hcont : Continuous (cubicPrimitive L S pieces) :=
    continuous_iff_continuousAt.mpr (fun t=>(trajectoryCheck_hasDerivAt L S pieces hcurve t).continuousAt)
  have hp := polynomialPieceCheck_global hpoly hparent.2.1
    (trajectoryCheck_lookup hcurve hpiece) (trajectoryCheck_continuousScore L S pieces hcurve)
    hcont hzp
  have hp' : parent.valuePolynomial.eval (parent.timeParameter z)=cubicPrimitive L S pieces z := by
    simpa only [ReferenceFlowCell.timeParameter,ReferenceFlowCell.length,Rat.cast_sub] using hp.1
  have hr := (ReferenceFlowCell.refinementCheck_fields href (child.timeParameter z)).2.2.2.2.2
  rw [←hg.2.2.2 z] at hr
  exact hr.trans hp'

theorem checked_refined_actual_weights {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (hc : c.check s k=true)
    {start finish lo hi L S : ℚ} {cells : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    {pieces : List CubicPiece}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck c.cell.flow lo hi=true) (hstart : c.start=start)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpiece : parent.canonicalPiece∈pieces) (hpoly : parent.canonicalPieceCheck=true)
    {Z : ℝ→ℝ}
    (herror : ∀ z∈Icc (start:ℝ) finish,
      |Z z-cubicPrimitive L S pieces z|≤(z-start)/2500000000)
    {z exponent terminal : ℝ}
    (hz : z∈Icc (c.cell.flow.segment.left.z:ℝ) c.cell.flow.segment.right.z)
    (he : c.cell.exponent.Contains s exponent) (hT : c.cell.terminal.Contains s terminal)
    (i : Fin 4) :
    (c.cell.weights i).Contains s
      (Real.exp exponent*(c.cell.flow.baseCoefficientExpr i).evalOne (c.cell.flow.timeParameter z)*
        (if i<2 then Z z else 1)/terminal) := by
  have hparent := referenceFlowCoverCheck_bounds hcover hmem
  have hg := ReferenceFlowCell.refinement_time_geometry href hparent.2.1
  have hwhole : z∈Icc (start:ℝ) finish :=
    ⟨(show (start:ℝ)≤c.cell.flow.segment.left.z by exact_mod_cast hparent.1.trans hg.2.1).trans hz.1,
      hz.2.trans (by exact_mod_cast hg.2.2.1.trans hparent.2.2)⟩
  have hvalue := refined_polynomial_global hcover hmem href hcurve hpiece hpoly hz
  have herr : |Z z-c.cell.flow.valuePolynomial.eval (c.cell.flow.timeParameter z)|≤
      (c.cell.flow.valueErrorRadius c.start:ℝ) := by
    rw [hvalue,hstart]
    exact ReferenceFlowCell.valueErrorRadius_of_global hz.2 (herror z hwhole)
  exact c.checked_weights hs hk hc (c.cell.flow.timeParameter_mem hg.1 hz) he herr hT i

end OptimalG.Certificates.Transport
