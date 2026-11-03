import OptimalG.Certificates.ReferenceFirstForceAssembly
import OptimalG.Certificates.ReferenceHessianWitnessData.CoarseLowerShape
import OptimalG.Certificates.ReferenceBudgetData.CoarseLowerShape
import OptimalG.Certificates.ReferencePositionData.CoarseLowerShape.Assembly
import OptimalG.Certificates.ReferenceForceRegularity
namespace OptimalG.Certificates.ReferenceFirstWitnessData.CoarseLowerShape
open Set MeasureTheory Transport
open scoped BigOperators
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem time_order : (ReferenceActualData.CoarseLowerShape.start:ℝ)≤ReferenceActualData.CoarseLowerShape.finish := by norm_num [ReferenceActualData.CoarseLowerShape.start,ReferenceActualData.CoarseLowerShape.finish]
theorem actual_adjoint {z : ℝ} (hz : z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) :
    ReferenceAdjointData.CoarseLowerShape.rho z=ReferencePositionData.CoarseLowerShape.exponential z*ReferenceAdjointData.CoarseLowerShape.Z z/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish := by
  exact Variational.affine_solution_adjoint_at time_order ReferenceActualData.CoarseLowerShape.alpha_intervalIntegrable ReferenceActualData.CoarseLowerShape.beta_intervalIntegrable
    ReferenceAdjointData.CoarseLowerShape.Z_spec.2.1 ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.2 ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.1 hz
theorem force_scalar {z : ℝ} (hz : z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) :
    ReferencePositionData.CoarseLowerShape.force 0 z=ReferenceAdjointData.CoarseLowerShape.rho z*(ReferenceBudgetData.CoarseLowerShape.alphaS z+ReferenceBudgetData.CoarseLowerShape.betaS z/ReferenceAdjointData.CoarseLowerShape.Z z) := by
  exact referenceCoordinateForce_scalar ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells ReferenceAdjointData.CoarseLowerShape.Z ReferencePositionData.CoarseLowerShape.exponential ReferenceAdjointData.CoarseLowerShape.rho
    (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) (ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.2 z hz).ne'
    (ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.2 ReferenceActualData.CoarseLowerShape.finish ⟨time_order,le_rfl⟩).ne' (actual_adjoint hz)
theorem force_scalar_integral :
    (∫ z in (ReferenceActualData.CoarseLowerShape.start:ℝ)..ReferenceActualData.CoarseLowerShape.finish,ReferencePositionData.CoarseLowerShape.force 0 z)=ReferenceBudgetData.CoarseLowerShape.V ReferenceActualData.CoarseLowerShape.finish/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish := by
  rw [←ReferenceBudgetData.CoarseLowerShape.scalar_integral_identity]
  apply intervalIntegral.integral_congr
  intro z hz
  exact force_scalar (by simpa only [uIcc_of_le time_order] using hz)
theorem exponential_continuous : ContinuousOn ReferencePositionData.CoarseLowerShape.exponential (uIcc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) := by
  have h := intervalIntegral.continuousOn_primitive_interval_left ((intervalIntegrable_iff').mp ReferenceActualData.CoarseLowerShape.alpha_intervalIntegrable)
  change ContinuousOn (Real.exp ∘ fun z : ℝ => ∫ x in z..(ReferenceActualData.CoarseLowerShape.finish:ℝ), ReferenceActualData.CoarseLowerShape.alpha x) _
  exact Real.continuous_exp.comp_continuousOn h
theorem force_scalar_integrable : IntervalIntegrable (ReferencePositionData.CoarseLowerShape.force 0) volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish := by
  have hi := ((ReferenceBudgetData.CoarseLowerShape.alphaS_intervalIntegrable.mul_continuousOn ReferenceAdjointData.CoarseLowerShape.Z_spec.2.1.continuousOn).add
    ReferenceBudgetData.CoarseLowerShape.betaS_intervalIntegrable).mul_continuousOn exponential_continuous
  change IntervalIntegrable (fun z=>ReferencePositionData.CoarseLowerShape.exponential z*(ReferenceBudgetData.CoarseLowerShape.alphaS z*ReferenceAdjointData.CoarseLowerShape.Z z+ReferenceBudgetData.CoarseLowerShape.betaS z)/ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) volume _ _
  convert hi.div_const (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) using 1
  funext z
  ring
theorem force_rank_integrable (j : Fin 16) (hj : j=1 ∨ j=2) :
    IntervalIntegrable (ReferencePositionData.CoarseLowerShape.force j) volume (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish := by
  apply referenceCoordinateForce_intervalIntegrable ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cells time_order
    (by simpa only [uIcc_of_le time_order] using ReferenceAdjointData.CoarseLowerShape.Z_spec.2.1.continuousOn)
    (by simpa only [uIcc_of_le time_order] using exponential_continuous) (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) j (B:=100)
  intro z hz
  rcases hj with rfl | rfl
  · exact (ReferencePositionData.CoarseLowerShape.Assembly.global_bounds hz).1
  · exact (ReferencePositionData.CoarseLowerShape.Assembly.global_bounds hz).2
theorem actual_first {p : ReferenceScalarCell×HessianCell} (hp : p∈ReferenceTimeData.CoarseLowerShape.Assembly.sources)
    {z : ℝ} (hz : z∈Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z)
    (ds eR eA : ℝ) :
    TransportHessianData.CoarseLowerShapeFlow.params.weightedFirst p.2.late (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) (ReferenceHessianWitnessData.CoarseLowerShape.frame p z)
      (FrozenParameters.threeDirection ds eR eA)=
        ds*ReferencePositionData.CoarseLowerShape.force 0 z+eR*ReferencePositionData.CoarseLowerShape.force 1 z+eA*ReferencePositionData.CoarseLowerShape.force 2 z := by
  have hg := ReferenceTimeData.CoarseLowerShape.Assembly.source_geometry p hp
  have hflow : p.1.flow∈ReferenceActualData.CoarseLowerShape.cells := by
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hb := referenceFlowCoverCheck_bounds ReferenceActualData.CoarseLowerShape.cover_checked hflow
  have hwhole : z∈Icc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish :=
    ⟨(show (ReferenceActualData.CoarseLowerShape.start:ℝ)≤p.1.flow.segment.left.z by exact_mod_cast hb.1).trans hz.1.le,
      hz.2.trans (by exact_mod_cast hb.2.2)⟩
  have hs0 : p.1.flow.slack=TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack := congrArg FrozenParameters.referenceSlack hg.1
  have hbase := ReferenceTimeData.CoarseLowerShape.Assembly.actual_frames p hp z hz
  have hb0 : ReferenceHessianWitnessData.CoarseLowerShape.frame p z 0=(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ) := by
    change (p.1.flow.slack:ℝ)=_; exact_mod_cast hs0
  have hS0 : (⟨TransportHessianData.CoarseLowerShapeFlow.start,TransportHessianData.CoarseLowerShapeFlow.finish⟩:IntegerInterval).Contains TransportHessianData.CoarseLowerShapeFlow.scale (ReferenceHessianWitnessData.CoarseLowerShape.frame p z 0) := by
    rw [hb0,←ReferenceHessianWitnessData.CoarseLowerShape.scalar_box_link]; exact ReferenceHessianWitnessData.CoarseLowerShape.reference_scalar_contains
  have hreg := HessianCell.checkedClean_source_regular TransportHessianData.CoarseLowerShapeFlow.scale_pos TransportHessianData.CoarseLowerShapeFlow.endpoints_ordered
    TransportHessianData.CoarseLowerShapeFlow.slabs_checked (ReferenceTimeData.CoarseLowerShape.Assembly.source_checked hp) hS0 hbase
  have hreg' : ∀ i∈FrozenParameters.activeTerms p.1.flow.late,
      p.1.params.sourceRegular p.1.flow.late i (ReferenceHessianWitnessData.CoarseLowerShape.frame p z) := by
    simpa only [hg.1,hg.2.1] using hreg
  have hf := reference_weighted_first_forces ReferenceSensitivityData.CoarseLowerShape.makeCell ReferenceActualData.CoarseLowerShape.cover_checked hflow (ReferenceTimeData.CoarseLowerShape.Assembly.source_scalar p hp)
    ReferenceAdjointData.CoarseLowerShape.Z ReferencePositionData.CoarseLowerShape.exponential ReferenceAdjointData.CoarseLowerShape.rho (ReferenceAdjointData.CoarseLowerShape.Z ReferenceActualData.CoarseLowerShape.finish) hz (ReferenceAdjointData.CoarseLowerShape.Z_spec.2.2.2.2 z hwhole)
    (actual_adjoint hwhole) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) (fun _=>rfl) hreg' ds eR eA
  simpa only [hg.1,hg.2.1,ReferenceHessianWitnessData.CoarseLowerShape.frame,ReferencePositionData.CoarseLowerShape.force] using hf
end OptimalG.Certificates.ReferenceFirstWitnessData.CoarseLowerShape
