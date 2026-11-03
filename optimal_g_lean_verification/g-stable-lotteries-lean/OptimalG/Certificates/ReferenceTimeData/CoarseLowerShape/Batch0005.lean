import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0005_0008
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0005_0008
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0009_0012
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Batch0005
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0003_0006
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Bundle0001_0004
namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0005
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch10_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0010.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0010.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch11_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0011.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0011.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile40_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r40=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds := by rfl
theorem a_profile40_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a40=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a40.bounds := by rfl
theorem r_fixed40_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 7 := by decide +kernel
theorem a_fixed40_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a40.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.a40.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 9 := by decide +kernel
theorem ranks40_linked : ReferenceRankData.CoarseLowerShape.Batch0005.targetR40=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0005.targetA40=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 1 := by decide +kernel
theorem r_input40_linked : ReferenceRankData.CoarseLowerShape.Batch0005.r40.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds.gauge] := by decide +kernel
theorem a_input40_linked : ReferenceRankData.CoarseLowerShape.Batch0005.a40.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.a40.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.a40.bounds.gauge] := by decide +kernel
theorem geometry40_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.a := by decide +kernel
theorem weights80_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0010.cert80.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights81_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0010.cert81.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time40_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 10)=true := by decide +kernel
theorem r_reference40_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 0)=true := by decide +kernel
theorem a_reference40_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 1)=true := by decide +kernel
theorem rank_r_link40_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r40 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link40_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0005.a40.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a40 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints40 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell true ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r40 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile40_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link40_checked
    geometry40_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell false ReferenceProfileData.CoarseLowerShape.Batch0005.a40.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a40 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile40_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link40_checked
    geometry40_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks40_linked.1,←ranks40_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0005.r40.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a40.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0005.ordered40_checked hr ha ho
theorem frozen_frame40 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40 ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds ReferenceProfileData.CoarseLowerShape.Batch0005.a40.bounds
  · rw [←r_profile40_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile40_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry40_linked.2.2.2.2.1
  · exact geometry40_linked.2.2.2.2.2
  · exact r_reference40_checked
  · exact a_reference40_checked
  · exact r_fixed40_linked
  · exact a_fixed40_linked
  · exact time40_checked
  · exact ht
  · exact hw
theorem child_geometry40_checked : ReferenceWeightData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights40 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0010.cert80∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch10_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0010.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0010.cert81∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch10_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0010.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry40_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights80_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry40_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry40_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights81_linked j (List.mem_finRange j))
theorem actual_frozen_frame40 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame40 (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.flow.timeParameter_mem child_geometry40_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights40 hz)
theorem r_profile41_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r41=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds := by rfl
theorem a_profile41_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a41=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a41.bounds := by rfl
theorem r_fixed41_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 7 := by decide +kernel
theorem a_fixed41_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a41.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.a41.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 9 := by decide +kernel
theorem ranks41_linked : ReferenceRankData.CoarseLowerShape.Batch0005.targetR41=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0005.targetA41=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 1 := by decide +kernel
theorem r_input41_linked : ReferenceRankData.CoarseLowerShape.Batch0005.r41.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds.gauge] := by decide +kernel
theorem a_input41_linked : ReferenceRankData.CoarseLowerShape.Batch0005.a41.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.a41.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.a41.bounds.gauge] := by decide +kernel
theorem geometry41_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.a := by decide +kernel
theorem weights82_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0010.cert82.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights83_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0010.cert83.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time41_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 10)=true := by decide +kernel
theorem r_reference41_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 0)=true := by decide +kernel
theorem a_reference41_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 1)=true := by decide +kernel
theorem rank_r_link41_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r41 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link41_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0005.a41.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a41 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints41 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell true ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r41 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile41_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link41_checked
    geometry41_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell false ReferenceProfileData.CoarseLowerShape.Batch0005.a41.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a41 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile41_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link41_checked
    geometry41_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks41_linked.1,←ranks41_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0005.r41.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a41.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0005.ordered41_checked hr ha ho
theorem frozen_frame41 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41 ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds ReferenceProfileData.CoarseLowerShape.Batch0005.a41.bounds
  · rw [←r_profile41_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile41_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry41_linked.2.2.2.2.1
  · exact geometry41_linked.2.2.2.2.2
  · exact r_reference41_checked
  · exact a_reference41_checked
  · exact r_fixed41_linked
  · exact a_fixed41_linked
  · exact time41_checked
  · exact ht
  · exact hw
theorem child_geometry41_checked : ReferenceWeightData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights41 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0010.cert82∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch10_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0010.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0010.cert83∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch10_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0010.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry41_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights82_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry41_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry41_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights83_linked j (List.mem_finRange j))
theorem actual_frozen_frame41 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame41 (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.flow.timeParameter_mem child_geometry41_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights41 hz)
theorem r_profile42_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r42=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds := by rfl
theorem a_profile42_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a42=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a42.bounds := by rfl
theorem r_fixed42_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 7 := by decide +kernel
theorem a_fixed42_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a42.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.a42.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 9 := by decide +kernel
theorem ranks42_linked : ReferenceRankData.CoarseLowerShape.Batch0005.targetR42=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0005.targetA42=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 1 := by decide +kernel
theorem r_input42_linked : ReferenceRankData.CoarseLowerShape.Batch0005.r42.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds.gauge] := by decide +kernel
theorem a_input42_linked : ReferenceRankData.CoarseLowerShape.Batch0005.a42.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.a42.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.a42.bounds.gauge] := by decide +kernel
theorem geometry42_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.a := by decide +kernel
theorem weights84_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0010.cert84.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights85_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0010.cert85.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time42_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 10)=true := by decide +kernel
theorem r_reference42_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 0)=true := by decide +kernel
theorem a_reference42_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 1)=true := by decide +kernel
theorem rank_r_link42_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r42 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link42_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0005.a42.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a42 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints42 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell true ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r42 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile42_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link42_checked
    geometry42_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell false ReferenceProfileData.CoarseLowerShape.Batch0005.a42.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a42 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile42_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link42_checked
    geometry42_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks42_linked.1,←ranks42_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0005.r42.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a42.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0005.ordered42_checked hr ha ho
theorem frozen_frame42 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42 ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds ReferenceProfileData.CoarseLowerShape.Batch0005.a42.bounds
  · rw [←r_profile42_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile42_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry42_linked.2.2.2.2.1
  · exact geometry42_linked.2.2.2.2.2
  · exact r_reference42_checked
  · exact a_reference42_checked
  · exact r_fixed42_linked
  · exact a_fixed42_linked
  · exact time42_checked
  · exact ht
  · exact hw
theorem child_geometry42_checked : ReferenceWeightData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights42 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0010.cert84∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch10_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0010.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0010.cert85∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch10_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0010.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry42_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights84_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry42_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry42_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights85_linked j (List.mem_finRange j))
theorem actual_frozen_frame42 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame42 (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.flow.timeParameter_mem child_geometry42_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights42 hz)
theorem r_profile43_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r43=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds := by rfl
theorem a_profile43_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a43=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a43.bounds := by rfl
theorem r_fixed43_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 7 := by decide +kernel
theorem a_fixed43_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a43.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.a43.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 9 := by decide +kernel
theorem ranks43_linked : ReferenceRankData.CoarseLowerShape.Batch0005.targetR43=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0005.targetA43=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 1 := by decide +kernel
theorem r_input43_linked : ReferenceRankData.CoarseLowerShape.Batch0005.r43.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds.gauge] := by decide +kernel
theorem a_input43_linked : ReferenceRankData.CoarseLowerShape.Batch0005.a43.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.a43.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.a43.bounds.gauge] := by decide +kernel
theorem geometry43_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.a := by decide +kernel
theorem weights86_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0010.cert86.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights87_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0010.cert87.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time43_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 10)=true := by decide +kernel
theorem r_reference43_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 0)=true := by decide +kernel
theorem a_reference43_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 1)=true := by decide +kernel
theorem rank_r_link43_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r43 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link43_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0005.a43.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a43 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints43 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell true ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r43 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile43_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link43_checked
    geometry43_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell false ReferenceProfileData.CoarseLowerShape.Batch0005.a43.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a43 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile43_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link43_checked
    geometry43_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks43_linked.1,←ranks43_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0005.r43.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a43.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0005.ordered43_checked hr ha ho
theorem frozen_frame43 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43 ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds ReferenceProfileData.CoarseLowerShape.Batch0005.a43.bounds
  · rw [←r_profile43_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile43_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry43_linked.2.2.2.2.1
  · exact geometry43_linked.2.2.2.2.2
  · exact r_reference43_checked
  · exact a_reference43_checked
  · exact r_fixed43_linked
  · exact a_fixed43_linked
  · exact time43_checked
  · exact ht
  · exact hw
theorem child_geometry43_checked : ReferenceWeightData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights43 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0010.cert86∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch10_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0010.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0010.cert87∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch10_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0010.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry43_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights86_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry43_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry43_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights87_linked j (List.mem_finRange j))
theorem actual_frozen_frame43 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame43 (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.flow.timeParameter_mem child_geometry43_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights43 hz)
theorem r_profile44_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r44=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds := by rfl
theorem a_profile44_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a44=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a44.bounds := by rfl
theorem r_fixed44_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 7 := by decide +kernel
theorem a_fixed44_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a44.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.a44.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 9 := by decide +kernel
theorem ranks44_linked : ReferenceRankData.CoarseLowerShape.Batch0005.targetR44=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0005.targetA44=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 1 := by decide +kernel
theorem r_input44_linked : ReferenceRankData.CoarseLowerShape.Batch0005.r44.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds.gauge] := by decide +kernel
theorem a_input44_linked : ReferenceRankData.CoarseLowerShape.Batch0005.a44.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.a44.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.a44.bounds.gauge] := by decide +kernel
theorem geometry44_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.a := by decide +kernel
theorem weights88_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0011.cert88.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights89_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0011.cert89.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time44_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 10)=true := by decide +kernel
theorem r_reference44_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 0)=true := by decide +kernel
theorem a_reference44_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 1)=true := by decide +kernel
theorem rank_r_link44_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r44 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link44_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0005.a44.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a44 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints44 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell true ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r44 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile44_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link44_checked
    geometry44_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell false ReferenceProfileData.CoarseLowerShape.Batch0005.a44.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a44 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile44_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link44_checked
    geometry44_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks44_linked.1,←ranks44_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0005.r44.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a44.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0005.ordered44_checked hr ha ho
theorem frozen_frame44 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44 ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds ReferenceProfileData.CoarseLowerShape.Batch0005.a44.bounds
  · rw [←r_profile44_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile44_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry44_linked.2.2.2.2.1
  · exact geometry44_linked.2.2.2.2.2
  · exact r_reference44_checked
  · exact a_reference44_checked
  · exact r_fixed44_linked
  · exact a_fixed44_linked
  · exact time44_checked
  · exact ht
  · exact hw
theorem child_geometry44_checked : ReferenceWeightData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights44 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0011.cert88∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch11_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0011.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0011.cert89∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch11_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0011.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry44_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights88_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry44_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry44_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights89_linked j (List.mem_finRange j))
theorem actual_frozen_frame44 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame44 (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.flow.timeParameter_mem child_geometry44_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights44 hz)
theorem r_profile45_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r45=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds := by rfl
theorem a_profile45_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a45=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a45.bounds := by rfl
theorem r_fixed45_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 7 := by decide +kernel
theorem a_fixed45_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a45.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.a45.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 9 := by decide +kernel
theorem ranks45_linked : ReferenceRankData.CoarseLowerShape.Batch0005.targetR45=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0005.targetA45=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 1 := by decide +kernel
theorem r_input45_linked : ReferenceRankData.CoarseLowerShape.Batch0005.r45.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds.gauge] := by decide +kernel
theorem a_input45_linked : ReferenceRankData.CoarseLowerShape.Batch0005.a45.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.a45.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.a45.bounds.gauge] := by decide +kernel
theorem geometry45_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.a := by decide +kernel
theorem weights90_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0011.cert90.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights91_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0011.cert91.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time45_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 10)=true := by decide +kernel
theorem r_reference45_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 0)=true := by decide +kernel
theorem a_reference45_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 1)=true := by decide +kernel
theorem rank_r_link45_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r45 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link45_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0005.a45.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a45 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints45 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell true ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r45 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile45_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link45_checked
    geometry45_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell false ReferenceProfileData.CoarseLowerShape.Batch0005.a45.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a45 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile45_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link45_checked
    geometry45_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks45_linked.1,←ranks45_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0005.r45.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a45.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0005.ordered45_checked hr ha ho
theorem frozen_frame45 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45 ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds ReferenceProfileData.CoarseLowerShape.Batch0005.a45.bounds
  · rw [←r_profile45_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile45_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry45_linked.2.2.2.2.1
  · exact geometry45_linked.2.2.2.2.2
  · exact r_reference45_checked
  · exact a_reference45_checked
  · exact r_fixed45_linked
  · exact a_fixed45_linked
  · exact time45_checked
  · exact ht
  · exact hw
theorem child_geometry45_checked : ReferenceWeightData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights45 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0011.cert90∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch11_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0011.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0011.cert91∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch11_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0011.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry45_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights90_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry45_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry45_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights91_linked j (List.mem_finRange j))
theorem actual_frozen_frame45 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame45 (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.flow.timeParameter_mem child_geometry45_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights45 hz)
theorem r_profile46_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r46=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds := by rfl
theorem a_profile46_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a46=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a46.bounds := by rfl
theorem r_fixed46_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 7 := by decide +kernel
theorem a_fixed46_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a46.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.a46.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 9 := by decide +kernel
theorem ranks46_linked : ReferenceRankData.CoarseLowerShape.Batch0005.targetR46=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0005.targetA46=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 1 := by decide +kernel
theorem r_input46_linked : ReferenceRankData.CoarseLowerShape.Batch0005.r46.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds.gauge] := by decide +kernel
theorem a_input46_linked : ReferenceRankData.CoarseLowerShape.Batch0005.a46.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.a46.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.a46.bounds.gauge] := by decide +kernel
theorem geometry46_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.a := by decide +kernel
theorem weights92_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0011.cert92.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights93_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0011.cert93.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time46_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 10)=true := by decide +kernel
theorem r_reference46_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 0)=true := by decide +kernel
theorem a_reference46_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 1)=true := by decide +kernel
theorem rank_r_link46_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r46 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link46_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0005.a46.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a46 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints46 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell true ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r46 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile46_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link46_checked
    geometry46_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell false ReferenceProfileData.CoarseLowerShape.Batch0005.a46.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a46 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile46_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link46_checked
    geometry46_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks46_linked.1,←ranks46_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0005.r46.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a46.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0005.ordered46_checked hr ha ho
theorem frozen_frame46 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46 ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds ReferenceProfileData.CoarseLowerShape.Batch0005.a46.bounds
  · rw [←r_profile46_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile46_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry46_linked.2.2.2.2.1
  · exact geometry46_linked.2.2.2.2.2
  · exact r_reference46_checked
  · exact a_reference46_checked
  · exact r_fixed46_linked
  · exact a_fixed46_linked
  · exact time46_checked
  · exact ht
  · exact hw
theorem child_geometry46_checked : ReferenceWeightData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights46 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0011.cert92∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch11_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0011.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0011.cert93∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch11_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0011.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry46_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights92_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry46_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry46_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights93_linked j (List.mem_finRange j))
theorem actual_frozen_frame46 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame46 (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.flow.timeParameter_mem child_geometry46_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights46 hz)
theorem r_profile47_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r47=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds := by rfl
theorem a_profile47_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a47=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a47.bounds := by rfl
theorem r_fixed47_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 7 := by decide +kernel
theorem a_fixed47_linked : ReferenceProfileData.CoarseLowerShape.Batch0005.a47.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0005.a47.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 9 := by decide +kernel
theorem ranks47_linked : ReferenceRankData.CoarseLowerShape.Batch0005.targetR47=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0005.targetA47=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 1 := by decide +kernel
theorem r_input47_linked : ReferenceRankData.CoarseLowerShape.Batch0005.r47.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds.gauge] := by decide +kernel
theorem a_input47_linked : ReferenceRankData.CoarseLowerShape.Batch0005.a47.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0005.a47.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0005.a47.bounds.gauge] := by decide +kernel
theorem geometry47_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.a := by decide +kernel
theorem weights94_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0011.cert94.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights95_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0011.cert95.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time47_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 10)=true := by decide +kernel
theorem r_reference47_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 0)=true := by decide +kernel
theorem a_reference47_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 1)=true := by decide +kernel
theorem rank_r_link47_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r47 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link47_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0005.a47.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a47 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints47 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell true ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds ReferenceRankData.CoarseLowerShape.Batch0005.r47 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile47_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link47_checked
    geometry47_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell false ReferenceProfileData.CoarseLowerShape.Batch0005.a47.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a47 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile47_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0005.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0005.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link47_checked
    geometry47_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks47_linked.1,←ranks47_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0005.r47.bounds ReferenceRankData.CoarseLowerShape.Batch0005.a47.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0005.ordered47_checked hr ha ho
theorem frozen_frame47 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47 ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds ReferenceProfileData.CoarseLowerShape.Batch0005.a47.bounds
  · rw [←r_profile47_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile47_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry47_linked.2.2.2.2.1
  · exact geometry47_linked.2.2.2.2.2
  · exact r_reference47_checked
  · exact a_reference47_checked
  · exact r_fixed47_linked
  · exact a_fixed47_linked
  · exact time47_checked
  · exact ht
  · exact hw
theorem child_geometry47_checked : ReferenceWeightData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights47 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0011.cert94∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch11_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0011.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0011.cert95∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch11_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0011.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry47_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights94_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry47_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry47_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights95_linked j (List.mem_finRange j))
theorem actual_frozen_frame47 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame47 (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.flow.timeParameter_mem child_geometry47_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights47 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell40),(ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell41),(ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell42),(ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell43),(ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell44),(ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell45),(ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell46),(ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0005.cell47)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0005.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0005.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame40 hz
  · exact fun z hz=>actual_frozen_frame41 hz
  · exact fun z hz=>actual_frozen_frame42 hz
  · exact fun z hz=>actual_frozen_frame43 hz
  · exact fun z hz=>actual_frozen_frame44 hz
  · exact fun z hz=>actual_frozen_frame45 hz
  · exact fun z hz=>actual_frozen_frame46 hz
  · exact fun z hz=>actual_frozen_frame47 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints40 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints41 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints42 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints43 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints44 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints45 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints46 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints47 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry40_linked.1,geometry40_linked.2.1,geometry40_linked.2.2.1,geometry40_linked.2.2.2.1⟩
  · exact ⟨geometry41_linked.1,geometry41_linked.2.1,geometry41_linked.2.2.1,geometry41_linked.2.2.2.1⟩
  · exact ⟨geometry42_linked.1,geometry42_linked.2.1,geometry42_linked.2.2.1,geometry42_linked.2.2.2.1⟩
  · exact ⟨geometry43_linked.1,geometry43_linked.2.1,geometry43_linked.2.2.1,geometry43_linked.2.2.2.1⟩
  · exact ⟨geometry44_linked.1,geometry44_linked.2.1,geometry44_linked.2.2.1,geometry44_linked.2.2.2.1⟩
  · exact ⟨geometry45_linked.1,geometry45_linked.2.1,geometry45_linked.2.2.1,geometry45_linked.2.2.2.1⟩
  · exact ⟨geometry46_linked.1,geometry46_linked.2.1,geometry46_linked.2.2.1,geometry46_linked.2.2.2.1⟩
  · exact ⟨geometry47_linked.1,geometry47_linked.2.1,geometry47_linked.2.2.1,geometry47_linked.2.2.2.1⟩
theorem rank_lower_checked : sources.all (fun p=>decide ((1/4:ℚ)≤p.1.flow.segment.left.r))=true := by decide +kernel
theorem branches_checked : sources.all (fun p=>p.1.branchGeometryCheck TransportReferenceData.CoarseLowerShape.data.leftContact)=true := by decide +kernel
theorem rank_crop_checked : sources.all (fun p=>p.1.flow.rankCropCheck TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact true && p.1.flow.rankCropCheck TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact false)=true := by decide +kernel
theorem source_rank_frames : ∀ p∈sources,∀ useR : Bool,∃ bounds : ReferenceProfileBox,
    (p.1.rankProfile useR bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true ∧
    (p.1.rankProfile useR bounds).lo≤(p.1.rankProfile useR bounds).hi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.a40.bounds,?_,geometry40_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a40.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile40_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds,?_,geometry40_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert40.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r40.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile40_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.a41.bounds,?_,geometry41_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a41.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile41_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds,?_,geometry41_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert41.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r41.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile41_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.a42.bounds,?_,geometry42_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a42.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile42_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds,?_,geometry42_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert42.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r42.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile42_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.a43.bounds,?_,geometry43_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a43.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile43_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds,?_,geometry43_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert43.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r43.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile43_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.a44.bounds,?_,geometry44_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a44.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile44_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds,?_,geometry44_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert44.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r44.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile44_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.a45.bounds,?_,geometry45_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a45.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile45_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds,?_,geometry45_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert45.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r45.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile45_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.a46.bounds,?_,geometry46_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a46.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile46_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds,?_,geometry46_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert46.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r46.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile46_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.a47.bounds,?_,geometry47_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0005.a47.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile47_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds,?_,geometry47_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0005.cert47.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0005.r47.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile47_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0005.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0005.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0005
