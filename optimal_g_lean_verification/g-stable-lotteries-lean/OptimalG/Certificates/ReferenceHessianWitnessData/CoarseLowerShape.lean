import OptimalG.Certificates.ReferenceChordRegular
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Assembly
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Summary
namespace OptimalG.Certificates.ReferenceHessianWitnessData.CoarseLowerShape
open Set MeasureTheory Transport
open scoped BigOperators
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem scalar_box_link : ReferenceProfileData.CoarseLowerShape.scalarBox=(⟨TransportHessianData.CoarseLowerShapeFlow.start,TransportHessianData.CoarseLowerShapeFlow.finish⟩:IntegerInterval) := by decide +kernel
theorem reference_scalar_contains : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains TransportHessianData.CoarseLowerShapeFlow.scale (TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ) := by
  norm_num [IntegerInterval.Contains,ReferenceProfileData.CoarseLowerShape.scalarBox,TransportHessianData.CoarseLowerShapeFlow.scale,TransportHessianData.CoarseLowerShapeFlow.params]
theorem compact_scalar_contains {S : ℝ} (hS : Compact.ScalarRange S) : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains TransportHessianData.CoarseLowerShapeFlow.scale S := by
  apply (IntegerInterval.contains_iff (by norm_num [TransportHessianData.CoarseLowerShapeFlow.scale]) _ _).mpr
  norm_num [IntegerInterval.toRat,RatInterval.Contains,ReferenceProfileData.CoarseLowerShape.scalarBox,TransportHessianData.CoarseLowerShapeFlow.scale,Compact.ScalarRange,Compact.scalarLower,Compact.scalarUpper] at hS ⊢
  constructor <;> linarith
noncomputable def frame (p : ReferenceScalarCell×HessianCell) (z : ℝ) : Fin 16→ℝ :=
  p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z)
theorem actual_cell_taylor {p : ReferenceScalarCell×HessianCell} (hp : p∈ReferenceTimeData.CoarseLowerShape.Assembly.sources)
    {S z r a : ℝ} {Jlow : ℝ→ℝ} (hS : Compact.ScalarRange S)
    (hz : z∈Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z)
    (hobstacle : ∀ v∈Icc (p.1.leftContact:ℝ) p.1.rightContact,
      quadratic p.1.flow.lam v-S≤Jlow v ∧ Jlow v≤cap p.1.flow.lam S v)
    (hR : p.1.primitiveMatch true S Jlow (p.1.flow.timeParameter z) r)
    (hA : p.1.primitiveMatch false S Jlow (p.1.flow.timeParameter z) a)
    (ho : if p.1.flow.late then a≤r else r≤a) :
    let ds := S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ)
    let eR := r-frame p z 1
    let eA := a-frame p z 2
    TransportHessianData.CoarseLowerShapeFlow.params.weightedFirst p.2.late (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) (frame p z)
        (FrozenParameters.threeDirection ds eR eA)+
      (TransportHessianData.CoarseLowerShapeFlow.scalarField z*ds^2-TransportHessianData.CoarseLowerShapeFlow.rankField z*(eR^2+eA^2))/2≤
        ∑ i∈FrozenParameters.activeTerms p.2.late,ReferenceAdjointData.CoarseLowerShape.weight i z*Real.log
          ((TransportHessianData.CoarseLowerShapeFlow.params.coefficients p.2.late i).eval
            (FrozenParameters.comparisonChord (frame p z) ds eR eA 1)/
           (TransportHessianData.CoarseLowerShapeFlow.params.coefficients p.2.late i).eval (frame p z)) := by
  have hg := ReferenceTimeData.CoarseLowerShape.Assembly.source_geometry p hp
  have hl : p.1.flow.lam=TransportHessianData.CoarseLowerShapeFlow.params.lam := congrArg FrozenParameters.lam hg.1
  have hs0 : p.1.flow.slack=TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack := congrArg FrozenParameters.referenceSlack hg.1
  have hL : Compact.LambdaRange p.1.flow.lam := by
    rw [hl]; norm_num [Compact.LambdaRange,TransportHessianData.CoarseLowerShapeFlow.params]
  have hSl : S≤(3:ℝ)/100 := by have hh:=hS.2; norm_num [Compact.scalarUpper] at hh; linarith
  have hflow : p.1.flow∈ReferenceActualData.CoarseLowerShape.cells := by
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have ht := p.1.flow.timeParameter_mem (referenceFlowCoverCheck_bounds ReferenceActualData.CoarseLowerShape.cover_checked hflow).2.1 ⟨hz.1.le,hz.2⟩
  have hend := ReferenceTimeData.CoarseLowerShape.Assembly.matched_endpoints p hp S Jlow hL hSl hobstacle (compact_scalar_contains hS)
    _ ht r a hR hA ho
  have hbase := ReferenceTimeData.CoarseLowerShape.Assembly.actual_frames p hp z hz
  have hb0 : frame p z 0=(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ) := by
    change (p.1.flow.slack:ℝ)=_
    exact_mod_cast hs0
  have hS0 : (⟨TransportHessianData.CoarseLowerShapeFlow.start,TransportHessianData.CoarseLowerShapeFlow.finish⟩:IntegerInterval).Contains TransportHessianData.CoarseLowerShapeFlow.scale (frame p z 0) := by
    rw [hb0,←scalar_box_link]
    exact reference_scalar_contains
  have hS1 : (⟨TransportHessianData.CoarseLowerShapeFlow.start,TransportHessianData.CoarseLowerShapeFlow.finish⟩:IntegerInterval).Contains TransportHessianData.CoarseLowerShapeFlow.scale
      (frame p z 0+(S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))) := by
    rw [hb0,show (TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ)+(S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))=S by ring,←scalar_box_link]
    exact compact_scalar_contains hS
  have hh := HessianCell.checkedClean_endpoint_chord_log_ratio TransportHessianData.CoarseLowerShapeFlow.scale_pos
    TransportHessianData.CoarseLowerShapeFlow.endpoints_ordered TransportHessianData.CoarseLowerShapeFlow.slabs_checked (ReferenceTimeData.CoarseLowerShape.Assembly.source_checked hp)
    (frame p z) (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ)) (r-frame p z 1) (a-frame p z 2)
    hS0 hS1 hbase (by simpa only [ReferenceSensitivityData.CoarseLowerShape.scale,TransportHessianData.CoarseLowerShapeFlow.scale,show frame p z 1 + (r-frame p z 1)=r by ring] using hend.1)
    (by simpa only [ReferenceSensitivityData.CoarseLowerShape.scale,TransportHessianData.CoarseLowerShapeFlow.scale,show frame p z 2 + (a-frame p z 2)=a by ring] using hend.2)
  have hm : p.2∈TransportHessianData.CoarseLowerShapeFlow.cells := by
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_hessians]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hzH : z∈Ioc (p.2.zLo:ℝ) p.2.zHi := by simpa only [hg.2.2.1,hg.2.2.2] using hz
  have hsField := hessianStepField_eq_of_mem TransportHessianData.CoarseLowerShapeFlow.time_cover_checked HessianCell.scalarLower hm hzH
  have hrField := hessianStepField_eq_of_mem TransportHessianData.CoarseLowerShapeFlow.time_cover_checked HessianCell.rankPenalty hm hzH
  have hw : (fun i : Fin 4=>frame p z ⟨12+i.val,by omega⟩)=(fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) := by
    funext i; fin_cases i <;> rfl
  have hw_point (i : Fin 4) : frame p z ⟨12+i.val,by omega⟩=ReferenceAdjointData.CoarseLowerShape.weight i z := congrFun hw i
  simpa only [hw,hw_point,TransportHessianData.CoarseLowerShapeFlow.scalarField,TransportHessianData.CoarseLowerShapeFlow.rankField,hsField,hrField] using hh
theorem actual_cell_regular {p : ReferenceScalarCell×HessianCell} (hp : p∈ReferenceTimeData.CoarseLowerShape.Assembly.sources)
    {S z r a : ℝ} {Jlow : ℝ→ℝ} (hS : Compact.ScalarRange S)
    (hz : z∈Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z)
    (hobstacle : ∀ v∈Icc (p.1.leftContact:ℝ) p.1.rightContact,
      quadratic p.1.flow.lam v-S≤Jlow v ∧ Jlow v≤cap p.1.flow.lam S v)
    (hR : p.1.primitiveMatch true S Jlow (p.1.flow.timeParameter z) r)
    (hA : p.1.primitiveMatch false S Jlow (p.1.flow.timeParameter z) a)
    (ho : if p.1.flow.late then a≤r else r≤a) :
    ∀ t∈Icc (0:ℝ) 1,∀ i∈FrozenParameters.activeTerms p.2.late,
      TransportHessianData.CoarseLowerShapeFlow.params.sourceRegular p.2.late i (FrozenParameters.comparisonChord (frame p z)
        (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ)) (r-frame p z 1) (a-frame p z 2) t) := by
  have hg := ReferenceTimeData.CoarseLowerShape.Assembly.source_geometry p hp
  have hl : p.1.flow.lam=TransportHessianData.CoarseLowerShapeFlow.params.lam := congrArg FrozenParameters.lam hg.1
  have hs0 : p.1.flow.slack=TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack := congrArg FrozenParameters.referenceSlack hg.1
  have hL : Compact.LambdaRange p.1.flow.lam := by
    rw [hl]; norm_num [Compact.LambdaRange,TransportHessianData.CoarseLowerShapeFlow.params]
  have hSl : S≤(3:ℝ)/100 := by have hh:=hS.2; norm_num [Compact.scalarUpper] at hh; linarith
  have hflow : p.1.flow∈ReferenceActualData.CoarseLowerShape.cells := by
    rw [←ReferenceTimeData.CoarseLowerShape.Assembly.source_cells]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have ht := p.1.flow.timeParameter_mem (referenceFlowCoverCheck_bounds ReferenceActualData.CoarseLowerShape.cover_checked hflow).2.1 ⟨hz.1.le,hz.2⟩
  have hend := ReferenceTimeData.CoarseLowerShape.Assembly.matched_endpoints p hp S Jlow hL hSl hobstacle (compact_scalar_contains hS)
    _ ht r a hR hA ho
  have hbase := ReferenceTimeData.CoarseLowerShape.Assembly.actual_frames p hp z hz
  have hb0 : frame p z 0=(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ) := by
    change (p.1.flow.slack:ℝ)=_
    exact_mod_cast hs0
  have hS0 : (⟨TransportHessianData.CoarseLowerShapeFlow.start,TransportHessianData.CoarseLowerShapeFlow.finish⟩:IntegerInterval).Contains TransportHessianData.CoarseLowerShapeFlow.scale (frame p z 0) := by
    rw [hb0,←scalar_box_link]
    exact reference_scalar_contains
  have hS1 : (⟨TransportHessianData.CoarseLowerShapeFlow.start,TransportHessianData.CoarseLowerShapeFlow.finish⟩:IntegerInterval).Contains TransportHessianData.CoarseLowerShapeFlow.scale
      (frame p z 0+(S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))) := by
    rw [hb0,show (TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ)+(S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ))=S by ring,←scalar_box_link]
    exact compact_scalar_contains hS
  exact HessianCell.checkedClean_endpoint_chord_regular TransportHessianData.CoarseLowerShapeFlow.scale_pos
    TransportHessianData.CoarseLowerShapeFlow.endpoints_ordered TransportHessianData.CoarseLowerShapeFlow.slabs_checked (ReferenceTimeData.CoarseLowerShape.Assembly.source_checked hp)
    (frame p z) (S-(TransportHessianData.CoarseLowerShapeFlow.params.referenceSlack:ℝ)) (r-frame p z 1) (a-frame p z 2)
    hS0 hS1 hbase (by simpa only [ReferenceSensitivityData.CoarseLowerShape.scale,TransportHessianData.CoarseLowerShapeFlow.scale,show frame p z 1 + (r-frame p z 1)=r by ring] using hend.1)
    (by simpa only [ReferenceSensitivityData.CoarseLowerShape.scale,TransportHessianData.CoarseLowerShapeFlow.scale,show frame p z 2 + (a-frame p z 2)=a by ring] using hend.2)
end OptimalG.Certificates.ReferenceHessianWitnessData.CoarseLowerShape
