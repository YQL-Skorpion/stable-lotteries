import OptimalG.Certificates.ReferenceAdjointWeights
import OptimalG.Certificates.ReferenceCoordinateForce
import OptimalG.Certificates.ReferencePositionTolerance

/-! The widened weight and force boxes enclose the same genuine global
reference adjoint and first-variation force, with an explicit flow error. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem checked_refined_adjoint_weights_with_error {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (error : ℚ) (hc : c.checkWithError s k error=true)
    {start finish lo hi L S : ℚ} {cells : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    {pieces : List CubicPiece}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck c.cell.flow lo hi=true)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpiece : parent.canonicalPiece∈pieces) (hpoly : parent.canonicalPieceCheck=true)
    {rate : ℝ} (hrate : 0≤rate)
    (hradius : rate*((c.cell.flow.segment.right.z:ℝ)-start)≤error)
    {Z : ℝ→ℝ}
    (herror : ∀ z∈Icc (start:ℝ) finish,
      |Z z-cubicPrimitive L S pieces z|≤rate*(z-start))
    (ha : IntervalIntegrable (referenceField ReferenceFlowCell.actualAlpha cells) volume
      (start:ℝ) finish)
    (hb : IntervalIntegrable (referenceField ReferenceFlowCell.actualBeta cells) volume
      (start:ℝ) finish)
    (hZ : AbsolutelyContinuousOnInterval Z start finish)
    (hpositive : ∀ z∈Icc (start:ℝ) finish,0<Z z)
    (hder : ∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),
      deriv Z z=referenceField ReferenceFlowCell.actualAlpha cells z*Z z+
        referenceField ReferenceFlowCell.actualBeta cells z)
    {z : ℝ} (hz : z∈Ioc (c.cell.flow.segment.left.z:ℝ) c.cell.flow.segment.right.z)
    (he : c.cell.exponent.Contains s
      (∫ x in z..(finish:ℝ),referenceField ReferenceFlowCell.actualAlpha cells x))
    (hT : c.cell.terminal.Contains s (Z finish)) (i : Fin 4) :
    (c.cell.weights i).Contains s
      (Variational.referenceIntegratingFactor start finish
        (fun t=>referenceField ReferenceFlowCell.actualBeta cells t/Z t) z*
       Variational.referenceWeight (referenceCoefficient cells i z)
        (Variational.transportDelta i) (Real.log (Z z))) := by
  have hp := referenceFlowCoverCheck_bounds hcover hmem
  have hg := ReferenceFlowCell.refinement_time_geometry href hp.2.1
  have hwhole : z∈Icc (start:ℝ) finish :=
    ⟨(show (start:ℝ)≤c.cell.flow.segment.left.z by exact_mod_cast hp.1.trans hg.2.1).trans hz.1.le,
      hz.2.trans (by exact_mod_cast hg.2.2.1.trans hp.2.2)⟩
  have horder : (start:ℝ)≤finish := by
    exact_mod_cast referenceFlowCoverCheck_order hcover
  have hweight := checked_refined_actual_weights_with_error hs hk c error hc hcover hmem href
    hcurve hpiece hpoly hrate hradius herror ⟨hz.1.le,hz.2⟩ he hT i
  rw [Variational.affine_solution_adjoint_at horder ha hb hZ hpositive hder hwhole,
    Variational.reference_weight_power (hpositive z hwhole) i,
    referenceCoefficient_on_refined_cell hcover hmem href hz i]
  convert hweight using 1 <;> split_ifs <;> first | omega | ring


theorem checked_global_refined_force_with_error {s multiplier k : ℕ}
    (hs : 0<s) (hm : 0<multiplier) (hk : 0<k)
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ f,(scalarFor f).flow=f)
    (c : ReferencePositionCell) (w : ReferenceWeightCertificate) (error : ℚ)
    (hc : c.check (multiplier*s) k=true) (hl : c.inputLinkCheckWithError s multiplier w error=true)
    (hcell : c.cell=scalarFor w.cell.flow)
    {start finish lo hi L S : ℚ} {coarse : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    {pieces : List CubicPiece}
    (hcover : referenceFlowCoverCheck start finish coarse=true) (hmem : parent∈coarse)
    (href : parent.refinementCheck w.cell.flow lo hi=true)
    (hmeta : ReferenceScalarCell.refinementMetadataCheck
      (scalarFor parent) (scalarFor w.cell.flow)=true)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpiece : parent.canonicalPiece∈pieces) (hpoly : parent.canonicalPieceCheck=true)
    {rate : ℝ} (hrate : 0≤rate)
    (hradius : rate*((w.cell.flow.segment.right.z:ℝ)-start)≤error)
    {Z E : ℝ→ℝ} {terminal z : ℝ}
    (herror : ∀ z∈Icc (start:ℝ) finish,
      |Z z-cubicPrimitive L S pieces z|≤rate*(z-start))
    (hz : z∈Ioc (w.cell.flow.segment.left.z:ℝ) w.cell.flow.segment.right.z)
    (hE : w.cell.exponential.Contains s (E z)) (hT : w.cell.terminal.Contains s terminal) :
    c.force.Contains (multiplier*s)
      (referenceCoordinateForce scalarFor coarse Z E terminal c.coordinate z) := by
  rw [referenceCoordinateForce_on_refined_cell scalarFor hscalar hcover hmem href
    hmeta Z E terminal c.coordinate hz]
  have hb := checked_refined_actual_force_with_error hs hm hk c w error hc hl hcover hmem href
    hcurve hpiece hpoly hrate hradius herror ⟨hz.1.le,hz.2⟩ hE hT
  simpa only [hcell,ReferenceScalarCell.coordinateAlpha,ReferenceScalarCell.coordinateBeta] using hb


end OptimalG.Certificates.Transport
