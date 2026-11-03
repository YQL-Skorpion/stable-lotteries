import OptimalG.Certificates.ReferenceWeightedInvariance
import OptimalG.Certificates.TransportFirstDecomposition
import OptimalG.Certificates.ReferenceCoordinateForce
import OptimalG.Certificates.ReferenceAdjointWeights

/-! The linear term of the checked coefficient Taylor estimate is the
first variation of the actual reference ODE, together with its two actual
rank forces. No independent linear-term enclosure is substituted here. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem HessianCell.checkedClean_source_regular {scale : ℕ} (hs : 0<scale)
    {params : FrozenParameters} {start finish : ℤ} {slabs : List IntegerInterval}
    {c : HessianCell} (horder : start<finish)
    (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.checkClean scale params slabs=true) {x : Fin 16→ℝ}
    (hS : (⟨start,finish⟩:IntegerInterval).Contains scale (x 0))
    (hfixed : ∀ i,(c.fixed i).Contains scale (x i.succ)) :
    ∀ i∈FrozenParameters.activeTerms c.late,params.sourceRegular c.late i x := by
  obtain ⟨box,hbox,hcheck⟩ := HessianCell.checkedClean_box_cover horder hslabs hc hS hfixed
  exact FrozenParameters.hessianCleanCheck_sourceRegular hs hbox hcheck

theorem referenceCoordinateForce_on_cell
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {c : ReferenceScalarCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : c.flow∈cells)
    (hcell : scalarFor c.flow=c) (Z E : ℝ→ℝ) (terminal : ℝ) (j : Fin 16)
    {z : ℝ} (hz : z∈Ioc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z) :
    referenceCoordinateForce scalarFor cells Z E terminal j z=
      (E z/terminal)*(Z z*c.coordinateAlpha j (c.flow.timeParameter z)+
        c.coordinateBeta j (c.flow.timeParameter z)) := by
  unfold referenceCoordinateForce
  rw [referenceField_on_cell _ hcover hmem hz,
    referenceField_on_cell _ hcover hmem hz,hcell]
  ring

theorem referenceCoefficient_on_cell_frozen
    {start finish : ℚ} {cells : List ReferenceFlowCell} {c : ReferenceScalarCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : c.flow∈cells)
    {z : ℝ} (hz : z∈Ioc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z) (i : Fin 4) :
    referenceCoefficient cells i z=
      (c.params.coefficients c.flow.late i).eval (c.frozenInput (c.flow.timeParameter z)) := by
  rw [referenceCoefficient,referenceField_on_cell _ hcover hmem hz]
  exact c.base_coefficient_identity i _

theorem reference_weighted_first_forces
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {c : ReferenceScalarCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : c.flow∈cells)
    (hcell : scalarFor c.flow=c) (Z E rho : ℝ→ℝ) (terminal : ℝ)
    {z : ℝ} (hz : z∈Ioc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z)
    (hZ : 0<Z z) (hrho : rho z=E z*Z z/terminal)
    (w : Fin 4→ℝ)
    (hw : ∀ i,w i=rho z*Variational.referenceWeight (referenceCoefficient cells i z)
      (Variational.transportDelta i) (Real.log (Z z)))
    (hregular : ∀ i∈FrozenParameters.activeTerms c.flow.late,
      c.params.sourceRegular c.flow.late i (c.weightedInput (c.flow.timeParameter z) w))
    (ds eR eA : ℝ) :
    c.params.weightedFirst c.flow.late w (c.weightedInput (c.flow.timeParameter z) w)
        (FrozenParameters.threeDirection ds eR eA)=
      ds*referenceCoordinateForce scalarFor cells Z E terminal 0 z+
      eR*referenceCoordinateForce scalarFor cells Z E terminal 1 z+
      eA*referenceCoordinateForce scalarFor cells Z E terminal 2 z := by
  have hreg : ∀ i∈FrozenParameters.activeTerms c.flow.late,
      c.params.sourceRegular c.flow.late i (c.frozenInput (c.flow.timeParameter z)) := by
    intro i hi
    exact (c.weightedInput_sourceRegular _ w _ i).mp (hregular i hi)
  have hweights : ∀ i∈FrozenParameters.activeTerms c.flow.late,
      w i=(E z/terminal)*FrozenParameters.referencePower (Z z) i*
        (c.params.coefficients c.flow.late i).eval (c.frozenInput (c.flow.timeParameter z)) := by
    intro i hi
    rw [hw i,hrho,Variational.reference_weight_power hZ i,
      referenceCoefficient_on_cell_frozen hcover hmem hz i]
    rfl
  rw [c.weightedInput_weightedFirst,c.weightedFirst_three_forces
    (c.flow.timeParameter z) (E z/terminal) (Z z) ds eR eA w hreg hweights]
  rw [referenceCoordinateForce_on_cell scalarFor hcover hmem hcell Z E terminal 0 hz,
    referenceCoordinateForce_on_cell scalarFor hcover hmem hcell Z E terminal 1 hz,
    referenceCoordinateForce_on_cell scalarFor hcover hmem hcell Z E terminal 2 hz]
  rfl

theorem referenceCoordinateForce_scalar
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell) (cells : List ReferenceFlowCell)
    (Z E rho : ℝ→ℝ) (terminal : ℝ) {z : ℝ}
    (hZ : Z z≠0) (hT : terminal≠0) (hrho : rho z=E z*Z z/terminal) :
    referenceCoordinateForce scalarFor cells Z E terminal 0 z=
      rho z*(referenceField (fun c=>(scalarFor c).actualAlphaS) cells z+
        referenceField (fun c=>(scalarFor c).actualBetaS) cells z/Z z) := by
  rw [hrho]
  change E z*(referenceField (fun c=>(scalarFor c).actualAlphaS) cells z*Z z+
      referenceField (fun c=>(scalarFor c).actualBetaS) cells z)/terminal=_
  field_simp [hZ,hT]

end OptimalG.Certificates.Transport
