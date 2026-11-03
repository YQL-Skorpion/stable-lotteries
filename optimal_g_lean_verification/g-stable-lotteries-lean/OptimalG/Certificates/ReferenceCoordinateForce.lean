import OptimalG.Certificates.ReferenceScalarRefinement
import OptimalG.Certificates.ReferenceRefinedPosition

/-! The positional force is a single function of the genuine reference flow.
Subdivision preserves its coordinate derivatives, rather than introducing
an unrelated function on each quadrature cell. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory
namespace ReferenceScalarCell

noncomputable def coordinateAlpha (c : ReferenceScalarCell) (j : Fin 16) (t : ℝ) : ℝ :=
  (RatExpr.partialExpr j c.alphaSource).eval (c.frozenInput t)

noncomputable def coordinateBeta (c : ReferenceScalarCell) (j : Fin 16) (t : ℝ) : ℝ :=
  (RatExpr.partialExpr j c.betaSource).eval (c.frozenInput t)

theorem coordinateAlpha_measurable (c : ReferenceScalarCell) (j : Fin 16) :
    Measurable (c.coordinateAlpha j) :=
  RatExpr.measurable_eval (fun i => RatExpr.measurable_evalOne (c.frozenSubstitution i)) _

theorem coordinateBeta_measurable (c : ReferenceScalarCell) (j : Fin 16) :
    Measurable (c.coordinateBeta j) :=
  RatExpr.measurable_eval (fun i => RatExpr.measurable_evalOne (c.frozenSubstitution i)) _

end ReferenceScalarCell

noncomputable def referenceCoordinateForce
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (Z E : ℝ→ℝ) (terminal : ℝ) (j : Fin 16) (z : ℝ) : ℝ :=
  E z*(referenceField (fun c => (scalarFor c).coordinateAlpha j) cells z*Z z+
    referenceField (fun c => (scalarFor c).coordinateBeta j) cells z)/terminal

theorem referenceCoordinateForce_measurable
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    {Z E : ℝ→ℝ} (hZ : Measurable Z) (hE : Measurable E) (terminal : ℝ) (j : Fin 16) :
    Measurable (referenceCoordinateForce scalarFor cells Z E terminal j) := by
  exact (hE.mul (((referenceField_measurable _
    (fun c => (scalarFor c).coordinateAlpha_measurable j) cells).mul hZ).add
      (referenceField_measurable _
        (fun c => (scalarFor c).coordinateBeta_measurable j) cells))).div_const terminal

theorem referenceCoordinateForce_on_refined_cell
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ f,(scalarFor f).flow=f)
    {start finish lo hi : ℚ} {cells : List ReferenceFlowCell}
    {parent child : ReferenceFlowCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck child lo hi=true)
    (hmeta : ReferenceScalarCell.refinementMetadataCheck
      (scalarFor parent) (scalarFor child)=true)
    (Z E : ℝ→ℝ) (terminal : ℝ) (j : Fin 16) {z : ℝ}
    (hz : z∈Ioc (child.segment.left.z:ℝ) child.segment.right.z) :
    referenceCoordinateForce scalarFor cells Z E terminal j z=
      E z*((scalarFor child).coordinateAlpha j (child.timeParameter z)*Z z+
        (scalarFor child).coordinateBeta j (child.timeParameter z))/terminal := by
  have hp := (referenceFlowCoverCheck_bounds hcover hmem).2.1
  have hzp := ReferenceFlowCell.refinement_mem_parent href hp hz
  have ht := (ReferenceFlowCell.refinement_time_geometry href hp).2.2.2 z
  have href' : (scalarFor parent).flow.refinementCheck (scalarFor child).flow lo hi=true := by
    simpa only [hscalar] using href
  have hf := ReferenceScalarCell.refinementCheck_coordinate_forces href' hmeta
    (child.timeParameter z) j
  unfold referenceCoordinateForce
  rw [referenceField_on_cell _ hcover hmem hzp,referenceField_on_cell _ hcover hmem hzp,ht]
  change E z*((RatExpr.partialExpr j (scalarFor parent).alphaSource).eval
      ((scalarFor parent).frozenInput ((lo:ℝ)+(hi-lo)*child.timeParameter z))*Z z+
    (RatExpr.partialExpr j (scalarFor parent).betaSource).eval
      ((scalarFor parent).frozenInput ((lo:ℝ)+(hi-lo)*child.timeParameter z)))/terminal=_
  rw [←hf.1,←hf.2]
  rfl

theorem checked_global_refined_force {s multiplier k : ℕ}
    (hs : 0<s) (hm : 0<multiplier) (hk : 0<k)
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ f,(scalarFor f).flow=f)
    (c : ReferencePositionCell) (w : ReferenceWeightCertificate)
    (hc : c.check (multiplier*s) k=true) (hl : c.inputLinkCheck s multiplier w=true)
    (hcell : c.cell=scalarFor w.cell.flow)
    {start finish lo hi L S : ℚ} {coarse : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    {pieces : List CubicPiece}
    (hcover : referenceFlowCoverCheck start finish coarse=true) (hmem : parent∈coarse)
    (href : parent.refinementCheck w.cell.flow lo hi=true) (hstart : w.start=start)
    (hmeta : ReferenceScalarCell.refinementMetadataCheck
      (scalarFor parent) (scalarFor w.cell.flow)=true)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpiece : parent.canonicalPiece∈pieces) (hpoly : parent.canonicalPieceCheck=true)
    {Z E : ℝ→ℝ} {terminal z : ℝ}
    (herror : ∀ z∈Icc (start:ℝ) finish,
      |Z z-cubicPrimitive L S pieces z|≤(z-start)/2500000000)
    (hz : z∈Ioc (w.cell.flow.segment.left.z:ℝ) w.cell.flow.segment.right.z)
    (hE : w.cell.exponential.Contains s (E z)) (hT : w.cell.terminal.Contains s terminal) :
    c.force.Contains (multiplier*s)
      (referenceCoordinateForce scalarFor coarse Z E terminal c.coordinate z) := by
  rw [referenceCoordinateForce_on_refined_cell scalarFor hscalar hcover hmem href
    hmeta Z E terminal c.coordinate hz]
  have hb := checked_refined_actual_force hs hm hk c w hc hl hcover hmem href hstart
    hcurve hpiece hpoly herror ⟨hz.1.le,hz.2⟩ hE hT
  simpa only [hcell,ReferenceScalarCell.coordinateAlpha,ReferenceScalarCell.coordinateBeta] using hb

end OptimalG.Certificates.Transport
