import OptimalG.Certificates.ReferenceCoefficientPairs
import OptimalG.Certificates.ReferenceTaylorData.CoarseLowerShape
namespace OptimalG.Certificates.ReferenceCoefficientPairData.CoarseLowerShape
open Set MeasureTheory Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem paired_on_cell {p : ReferenceScalarCell×HessianCell} (hp : p∈ReferenceTimeData.CoarseLowerShape.Assembly.sources)
    {S z : ℝ} (hS : Compact.ScalarRange S) (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hz : z∈Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z)
    (hobstacle : ∀ r∈Icc (p.1.leftContact:ℝ) p.1.rightContact,
      quadratic p.1.flow.lam r-S≤Jlow r ∧ Jlow r≤cap p.1.flow.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧
      Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r) (i : Fin 4) :
    ((ReferenceTaylorData.CoarseLowerShape.coefficient S G i z=0 ∧ ReferenceAdjointData.CoarseLowerShape.coefficient i z=0) ∨
      (0<ReferenceTaylorData.CoarseLowerShape.coefficient S G i z ∧ 0<ReferenceAdjointData.CoarseLowerShape.coefficient i z)) := by
  have hg := ReferenceTimeData.CoarseLowerShape.Assembly.source_geometry p hp
  have hflow : p.1.flow∈ReferenceActualData.CoarseLowerShape.cells := by
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hb := referenceFlowCoverCheck_bounds ReferenceActualData.CoarseLowerShape.cover_checked hflow
  have ht := p.1.flow.timeParameter_mem hb.2.1 ⟨hz.1.le,hz.2⟩
  have hwhole : z∈Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish :=
    ⟨(show (ReferenceActualData.CoarseLowerShape.start:ℝ)≤p.1.flow.segment.left.z by exact_mod_cast hb.1).trans_lt hz.1,
      hz.2.trans (by exact_mod_cast hb.2.2)⟩
  have hmatched (useR : Bool) : p.1.primitiveMatch useR S Jlow (p.1.flow.timeParameter z)
      (p.1.globalMatchedRank useR G (p.1.flow.timeParameter z)) := by
    obtain ⟨bounds,hframe,horder⟩ := ReferenceTimeData.CoarseLowerShape.Assembly.source_rank_frames p hp useR
    exact ReferenceScalarCell.primitiveMatch_of_global_matching TransportReferenceData.CoarseLowerShape.data ReferenceLowData.CoarseLowerShape.checked
      TransportReferenceData.CoarseLowerShape.gauge_checked p.1 useR bounds hframe horder hmatch ht
  have hregular := ReferenceHessianWitnessData.CoarseLowerShape.actual_cell_regular hp hS hz hobstacle (hmatched true) (hmatched false)
    (ReferenceTaylorData.CoarseLowerShape.matched_order hp G (fun r hr=>(hmatch r hr).1) ht)
  have href (j : Fin 4) : ReferenceAdjointData.CoarseLowerShape.coefficient j z=
      (TransportHessianData.CoarseLowerShapeFlow.params.coefficients p.2.late j).eval (ReferenceHessianWitnessData.CoarseLowerShape.frame p z) := by
    rw [ReferenceAdjointData.CoarseLowerShape.coefficient,referenceCoefficient_on_cell_frozen ReferenceActualData.CoarseLowerShape.cover_checked hflow hz j,
      ←p.1.weightedInput_coefficient (p.1.flow.timeParameter z) (fun k=>ReferenceAdjointData.CoarseLowerShape.weight k z) j]
    simp only [ReferenceHessianWitnessData.CoarseLowerShape.frame,hg.1,hg.2.1]
  have hrho : 0<ReferenceAdjointData.CoarseLowerShape.rho z := Variational.referenceIntegratingFactor_pos _ _ _ _
  have hw (j : Fin 4) : 0≤ReferenceAdjointData.CoarseLowerShape.rho z*Variational.referenceWeight
      ((TransportHessianData.CoarseLowerShapeFlow.params.coefficients p.2.late j).eval (ReferenceHessianWitnessData.CoarseLowerShape.frame p z))
      (Variational.transportDelta j) (Real.log (ReferenceAdjointData.CoarseLowerShape.Z z)) := by
    rw [←href j]
    exact ReferenceAdjointData.CoarseLowerShape.weights_nonnegative hwhole j
  have hpairs := TransportHessianData.CoarseLowerShapeFlow.params.chord_coefficient_pair p.2.late (ReferenceHessianWitnessData.CoarseLowerShape.frame p z)
    (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))
    (p.1.globalMatchedRank true G (p.1.flow.timeParameter z)-ReferenceHessianWitnessData.CoarseLowerShape.frame p z 1)
    (p.1.globalMatchedRank false G (p.1.flow.timeParameter z)-ReferenceHessianWitnessData.CoarseLowerShape.frame p z 2)
    (ReferenceAdjointData.CoarseLowerShape.rho z) (Real.log (ReferenceAdjointData.CoarseLowerShape.Z z)) Variational.transportDelta hrho hw hregular i
  have hs0 : p.1.flow.slack=TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack := congrArg FrozenParameters.referenceSlack hg.1
  have hactual : ReferenceTaylorData.CoarseLowerShape.coefficient S G i z=
      (TransportHessianData.CoarseLowerShapeFlow.params.coefficients p.2.late i).eval
        (FrozenParameters.comparisonChord (ReferenceHessianWitnessData.CoarseLowerShape.frame p z) (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))
          (p.1.globalMatchedRank true G (p.1.flow.timeParameter z)-ReferenceHessianWitnessData.CoarseLowerShape.frame p z 1)
          (p.1.globalMatchedRank false G (p.1.flow.timeParameter z)-ReferenceHessianWitnessData.CoarseLowerShape.frame p z 2) 1) := by
    have hh := referenceMatchedCoefficient_on_cell ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cover_checked hflow
      (ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp) S G hz (fun j=>ReferenceAdjointData.CoarseLowerShape.weight j z) i
    simpa only [ReferenceTaylorData.CoarseLowerShape.coefficient,ReferenceScalarCell.endpointChord,ReferenceHessianWitnessData.CoarseLowerShape.frame,hg.1,hg.2.1,hs0] using hh
  simpa only [←hactual,←href i] using hpairs
theorem paired {S : ℝ} (hS : Compact.ScalarRange S) (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hobstacle : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,
      quadratic TransportReferenceData.CoarseLowerShape.data.lam r-S≤Jlow r ∧ Jlow r≤cap TransportReferenceData.CoarseLowerShape.data.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧
      Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r)
    {z : ℝ} (hz : z∈Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) (i : Fin 4) :
    ((ReferenceTaylorData.CoarseLowerShape.coefficient S G i z=0 ∧ ReferenceAdjointData.CoarseLowerShape.coefficient i z=0) ∨
      (0<ReferenceTaylorData.CoarseLowerShape.coefficient S G i z ∧ 0<ReferenceAdjointData.CoarseLowerShape.coefficient i z)) := by
  obtain ⟨p,hp,hzp,_⟩ := ReferenceTimeData.CoarseLowerShape.Assembly.selected_actual_frame hz
  apply paired_on_cell hp hS G hzp _ hmatch i
  have hs := ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp
  have hl : p.1.leftContact=TransportReferenceData.CoarseLowerShape.data.leftContact := by rw [←hs]; rfl
  have hr : p.1.rightContact=TransportReferenceData.CoarseLowerShape.data.rightContact := by rw [←hs]; rfl
  have hL : p.1.flow.lam=TransportReferenceData.CoarseLowerShape.data.lam := congrArg FrozenParameters.lam (ReferenceTimeData.CoarseLowerShape.Assembly.source_geometry p hp).1
  simpa only [hl,hr,hL,ReferenceDisplacementData.CoarseLowerShape.left,ReferenceDisplacementData.CoarseLowerShape.right] using hobstacle
theorem paired_ae {S : ℝ} (hS : Compact.ScalarRange S) (G : StieltjesFunction ℝ) {Jlow : ℝ→ℝ}
    (hobstacle : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,
      quadratic TransportReferenceData.CoarseLowerShape.data.lam r-S≤Jlow r ∧ Jlow r≤cap TransportReferenceData.CoarseLowerShape.data.lam S r)
    (hmatch : ∀ r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right,G r∈Icc ReferenceDisplacementData.CoarseLowerShape.left ReferenceDisplacementData.CoarseLowerShape.right ∧
      Jlow (G r)=TransportReferenceData.CoarseLowerShape.data.transportPrimitive S r) :
    ∀ᵐ z ∂volume.restrict (Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish),∀ i,
      ((ReferenceTaylorData.CoarseLowerShape.coefficient S G i z=0 ∧ ReferenceAdjointData.CoarseLowerShape.coefficient i z=0) ∨
        (0<ReferenceTaylorData.CoarseLowerShape.coefficient S G i z ∧ 0<ReferenceAdjointData.CoarseLowerShape.coefficient i z)) := by
  rw [←Measure.restrict_congr_set Ioc_ae_eq_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
  exact paired hS G hobstacle hmatch hz
end OptimalG.Certificates.ReferenceCoefficientPairData.CoarseLowerShape
