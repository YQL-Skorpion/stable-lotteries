import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0005_0008
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0005_0008
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0013_0016
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Batch0006
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0003_0006
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0005
namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0006
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch12_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0012.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0012.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch13_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0013.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0013.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile48_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r48=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds := by rfl
theorem a_profile48_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a48=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a48.bounds := by rfl
theorem r_fixed48_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 7 := by decide +kernel
theorem a_fixed48_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a48.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.a48.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 9 := by decide +kernel
theorem ranks48_linked : ReferenceRankData.CoarseLowerShape.Batch0006.targetR48=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0006.targetA48=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 1 := by decide +kernel
theorem r_input48_linked : ReferenceRankData.CoarseLowerShape.Batch0006.r48.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds.gauge] := by decide +kernel
theorem a_input48_linked : ReferenceRankData.CoarseLowerShape.Batch0006.a48.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.a48.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.a48.bounds.gauge] := by decide +kernel
theorem geometry48_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.a := by decide +kernel
theorem weights96_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0012.cert96.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights97_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0012.cert97.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time48_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 10)=true := by decide +kernel
theorem r_reference48_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 0)=true := by decide +kernel
theorem a_reference48_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 1)=true := by decide +kernel
theorem rank_r_link48_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r48 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link48_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0006.a48.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a48 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints48 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell true ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r48 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile48_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link48_checked
    geometry48_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell false ReferenceProfileData.CoarseLowerShape.Batch0006.a48.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a48 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile48_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link48_checked
    geometry48_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks48_linked.1,←ranks48_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0006.r48.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a48.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0006.ordered48_checked hr ha ho
theorem frozen_frame48 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48 ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds ReferenceProfileData.CoarseLowerShape.Batch0006.a48.bounds
  · rw [←r_profile48_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile48_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry48_linked.2.2.2.2.1
  · exact geometry48_linked.2.2.2.2.2
  · exact r_reference48_checked
  · exact a_reference48_checked
  · exact r_fixed48_linked
  · exact a_fixed48_linked
  · exact time48_checked
  · exact ht
  · exact hw
theorem child_geometry48_checked : ReferenceWeightData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights48 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0012.cert96∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch12_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0012.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0012.cert97∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch12_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0012.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry48_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights96_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry48_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry48_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights97_linked j (List.mem_finRange j))
theorem actual_frozen_frame48 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame48 (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.flow.timeParameter_mem child_geometry48_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights48 hz)
theorem r_profile49_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r49=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds := by rfl
theorem a_profile49_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a49=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a49.bounds := by rfl
theorem r_fixed49_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 7 := by decide +kernel
theorem a_fixed49_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a49.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.a49.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 9 := by decide +kernel
theorem ranks49_linked : ReferenceRankData.CoarseLowerShape.Batch0006.targetR49=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0006.targetA49=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 1 := by decide +kernel
theorem r_input49_linked : ReferenceRankData.CoarseLowerShape.Batch0006.r49.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds.gauge] := by decide +kernel
theorem a_input49_linked : ReferenceRankData.CoarseLowerShape.Batch0006.a49.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.a49.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.a49.bounds.gauge] := by decide +kernel
theorem geometry49_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.a := by decide +kernel
theorem weights98_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0012.cert98.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights99_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0012.cert99.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time49_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 10)=true := by decide +kernel
theorem r_reference49_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 0)=true := by decide +kernel
theorem a_reference49_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 1)=true := by decide +kernel
theorem rank_r_link49_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r49 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link49_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0006.a49.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a49 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints49 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell true ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r49 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile49_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link49_checked
    geometry49_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell false ReferenceProfileData.CoarseLowerShape.Batch0006.a49.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a49 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile49_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link49_checked
    geometry49_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks49_linked.1,←ranks49_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0006.r49.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a49.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0006.ordered49_checked hr ha ho
theorem frozen_frame49 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49 ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds ReferenceProfileData.CoarseLowerShape.Batch0006.a49.bounds
  · rw [←r_profile49_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile49_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry49_linked.2.2.2.2.1
  · exact geometry49_linked.2.2.2.2.2
  · exact r_reference49_checked
  · exact a_reference49_checked
  · exact r_fixed49_linked
  · exact a_fixed49_linked
  · exact time49_checked
  · exact ht
  · exact hw
theorem child_geometry49_checked : ReferenceWeightData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights49 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0012.cert98∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch12_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0012.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0012.cert99∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch12_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0012.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry49_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights98_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry49_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry49_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights99_linked j (List.mem_finRange j))
theorem actual_frozen_frame49 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame49 (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.flow.timeParameter_mem child_geometry49_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights49 hz)
theorem r_profile50_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r50=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds := by rfl
theorem a_profile50_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a50=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a50.bounds := by rfl
theorem r_fixed50_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 7 := by decide +kernel
theorem a_fixed50_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a50.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.a50.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 9 := by decide +kernel
theorem ranks50_linked : ReferenceRankData.CoarseLowerShape.Batch0006.targetR50=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0006.targetA50=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 1 := by decide +kernel
theorem r_input50_linked : ReferenceRankData.CoarseLowerShape.Batch0006.r50.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds.gauge] := by decide +kernel
theorem a_input50_linked : ReferenceRankData.CoarseLowerShape.Batch0006.a50.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.a50.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.a50.bounds.gauge] := by decide +kernel
theorem geometry50_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.a := by decide +kernel
theorem weights100_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0012.cert100.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights101_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0012.cert101.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time50_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 10)=true := by decide +kernel
theorem r_reference50_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 0)=true := by decide +kernel
theorem a_reference50_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 1)=true := by decide +kernel
theorem rank_r_link50_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r50 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link50_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0006.a50.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a50 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints50 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell true ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r50 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile50_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link50_checked
    geometry50_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell false ReferenceProfileData.CoarseLowerShape.Batch0006.a50.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a50 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile50_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link50_checked
    geometry50_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks50_linked.1,←ranks50_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0006.r50.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a50.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0006.ordered50_checked hr ha ho
theorem frozen_frame50 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50 ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds ReferenceProfileData.CoarseLowerShape.Batch0006.a50.bounds
  · rw [←r_profile50_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile50_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry50_linked.2.2.2.2.1
  · exact geometry50_linked.2.2.2.2.2
  · exact r_reference50_checked
  · exact a_reference50_checked
  · exact r_fixed50_linked
  · exact a_fixed50_linked
  · exact time50_checked
  · exact ht
  · exact hw
theorem child_geometry50_checked : ReferenceWeightData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights50 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0012.cert100∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch12_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0012.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0012.cert101∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch12_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0012.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry50_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights100_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry50_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry50_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights101_linked j (List.mem_finRange j))
theorem actual_frozen_frame50 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame50 (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.flow.timeParameter_mem child_geometry50_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights50 hz)
theorem r_profile51_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r51=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds := by rfl
theorem a_profile51_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a51=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a51.bounds := by rfl
theorem r_fixed51_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 7 := by decide +kernel
theorem a_fixed51_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a51.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.a51.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 9 := by decide +kernel
theorem ranks51_linked : ReferenceRankData.CoarseLowerShape.Batch0006.targetR51=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0006.targetA51=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 1 := by decide +kernel
theorem r_input51_linked : ReferenceRankData.CoarseLowerShape.Batch0006.r51.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds.gauge] := by decide +kernel
theorem a_input51_linked : ReferenceRankData.CoarseLowerShape.Batch0006.a51.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.a51.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.a51.bounds.gauge] := by decide +kernel
theorem geometry51_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.a := by decide +kernel
theorem weights102_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0012.cert102.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights103_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0012.cert103.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time51_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 10)=true := by decide +kernel
theorem r_reference51_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 0)=true := by decide +kernel
theorem a_reference51_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 1)=true := by decide +kernel
theorem rank_r_link51_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r51 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link51_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0006.a51.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a51 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints51 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell true ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r51 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile51_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link51_checked
    geometry51_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell false ReferenceProfileData.CoarseLowerShape.Batch0006.a51.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a51 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile51_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link51_checked
    geometry51_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks51_linked.1,←ranks51_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0006.r51.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a51.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0006.ordered51_checked hr ha ho
theorem frozen_frame51 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51 ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds ReferenceProfileData.CoarseLowerShape.Batch0006.a51.bounds
  · rw [←r_profile51_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile51_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry51_linked.2.2.2.2.1
  · exact geometry51_linked.2.2.2.2.2
  · exact r_reference51_checked
  · exact a_reference51_checked
  · exact r_fixed51_linked
  · exact a_fixed51_linked
  · exact time51_checked
  · exact ht
  · exact hw
theorem child_geometry51_checked : ReferenceWeightData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights51 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0012.cert102∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch12_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0012.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0012.cert103∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch12_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0012.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry51_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights102_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry51_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry51_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights103_linked j (List.mem_finRange j))
theorem actual_frozen_frame51 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame51 (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.flow.timeParameter_mem child_geometry51_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights51 hz)
theorem r_profile52_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r52=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds := by rfl
theorem a_profile52_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a52=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a52.bounds := by rfl
theorem r_fixed52_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 7 := by decide +kernel
theorem a_fixed52_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a52.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.a52.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 9 := by decide +kernel
theorem ranks52_linked : ReferenceRankData.CoarseLowerShape.Batch0006.targetR52=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0006.targetA52=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 1 := by decide +kernel
theorem r_input52_linked : ReferenceRankData.CoarseLowerShape.Batch0006.r52.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds.gauge] := by decide +kernel
theorem a_input52_linked : ReferenceRankData.CoarseLowerShape.Batch0006.a52.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.a52.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.a52.bounds.gauge] := by decide +kernel
theorem geometry52_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.a := by decide +kernel
theorem weights104_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0013.cert104.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights105_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0013.cert105.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time52_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 10)=true := by decide +kernel
theorem r_reference52_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 0)=true := by decide +kernel
theorem a_reference52_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 1)=true := by decide +kernel
theorem rank_r_link52_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r52 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link52_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0006.a52.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a52 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints52 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell true ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r52 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile52_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link52_checked
    geometry52_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell false ReferenceProfileData.CoarseLowerShape.Batch0006.a52.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a52 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile52_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link52_checked
    geometry52_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks52_linked.1,←ranks52_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0006.r52.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a52.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0006.ordered52_checked hr ha ho
theorem frozen_frame52 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52 ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds ReferenceProfileData.CoarseLowerShape.Batch0006.a52.bounds
  · rw [←r_profile52_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile52_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry52_linked.2.2.2.2.1
  · exact geometry52_linked.2.2.2.2.2
  · exact r_reference52_checked
  · exact a_reference52_checked
  · exact r_fixed52_linked
  · exact a_fixed52_linked
  · exact time52_checked
  · exact ht
  · exact hw
theorem child_geometry52_checked : ReferenceWeightData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights52 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0013.cert104∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch13_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0013.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0013.cert105∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch13_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0013.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry52_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights104_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry52_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry52_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights105_linked j (List.mem_finRange j))
theorem actual_frozen_frame52 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame52 (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.flow.timeParameter_mem child_geometry52_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights52 hz)
theorem r_profile53_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r53=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds := by rfl
theorem a_profile53_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a53=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a53.bounds := by rfl
theorem r_fixed53_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 7 := by decide +kernel
theorem a_fixed53_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a53.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.a53.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 9 := by decide +kernel
theorem ranks53_linked : ReferenceRankData.CoarseLowerShape.Batch0006.targetR53=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0006.targetA53=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 1 := by decide +kernel
theorem r_input53_linked : ReferenceRankData.CoarseLowerShape.Batch0006.r53.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds.gauge] := by decide +kernel
theorem a_input53_linked : ReferenceRankData.CoarseLowerShape.Batch0006.a53.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.a53.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.a53.bounds.gauge] := by decide +kernel
theorem geometry53_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.a := by decide +kernel
theorem weights106_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0013.cert106.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights107_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0013.cert107.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time53_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 10)=true := by decide +kernel
theorem r_reference53_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 0)=true := by decide +kernel
theorem a_reference53_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 1)=true := by decide +kernel
theorem rank_r_link53_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r53 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link53_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0006.a53.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a53 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints53 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell true ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r53 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile53_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link53_checked
    geometry53_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell false ReferenceProfileData.CoarseLowerShape.Batch0006.a53.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a53 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile53_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link53_checked
    geometry53_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks53_linked.1,←ranks53_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0006.r53.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a53.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0006.ordered53_checked hr ha ho
theorem frozen_frame53 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53 ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds ReferenceProfileData.CoarseLowerShape.Batch0006.a53.bounds
  · rw [←r_profile53_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile53_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry53_linked.2.2.2.2.1
  · exact geometry53_linked.2.2.2.2.2
  · exact r_reference53_checked
  · exact a_reference53_checked
  · exact r_fixed53_linked
  · exact a_fixed53_linked
  · exact time53_checked
  · exact ht
  · exact hw
theorem child_geometry53_checked : ReferenceWeightData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights53 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0013.cert106∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch13_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0013.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0013.cert107∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch13_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0013.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry53_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights106_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry53_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry53_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights107_linked j (List.mem_finRange j))
theorem actual_frozen_frame53 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame53 (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.flow.timeParameter_mem child_geometry53_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights53 hz)
theorem r_profile54_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r54=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds := by rfl
theorem a_profile54_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a54=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a54.bounds := by rfl
theorem r_fixed54_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 7 := by decide +kernel
theorem a_fixed54_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a54.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.a54.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 9 := by decide +kernel
theorem ranks54_linked : ReferenceRankData.CoarseLowerShape.Batch0006.targetR54=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0006.targetA54=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 1 := by decide +kernel
theorem r_input54_linked : ReferenceRankData.CoarseLowerShape.Batch0006.r54.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds.gauge] := by decide +kernel
theorem a_input54_linked : ReferenceRankData.CoarseLowerShape.Batch0006.a54.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.a54.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.a54.bounds.gauge] := by decide +kernel
theorem geometry54_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.a := by decide +kernel
theorem weights108_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0013.cert108.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights109_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0013.cert109.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time54_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 10)=true := by decide +kernel
theorem r_reference54_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 0)=true := by decide +kernel
theorem a_reference54_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 1)=true := by decide +kernel
theorem rank_r_link54_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r54 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link54_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0006.a54.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a54 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints54 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell true ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r54 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile54_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link54_checked
    geometry54_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell false ReferenceProfileData.CoarseLowerShape.Batch0006.a54.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a54 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile54_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link54_checked
    geometry54_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks54_linked.1,←ranks54_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0006.r54.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a54.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0006.ordered54_checked hr ha ho
theorem frozen_frame54 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54 ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds ReferenceProfileData.CoarseLowerShape.Batch0006.a54.bounds
  · rw [←r_profile54_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile54_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry54_linked.2.2.2.2.1
  · exact geometry54_linked.2.2.2.2.2
  · exact r_reference54_checked
  · exact a_reference54_checked
  · exact r_fixed54_linked
  · exact a_fixed54_linked
  · exact time54_checked
  · exact ht
  · exact hw
theorem child_geometry54_checked : ReferenceWeightData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights54 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0013.cert108∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch13_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0013.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0013.cert109∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch13_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0013.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry54_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights108_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry54_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry54_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights109_linked j (List.mem_finRange j))
theorem actual_frozen_frame54 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame54 (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.flow.timeParameter_mem child_geometry54_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights54 hz)
theorem r_profile55_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r55=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds := by rfl
theorem a_profile55_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a55=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a55.bounds := by rfl
theorem r_fixed55_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 7 := by decide +kernel
theorem a_fixed55_linked : ReferenceProfileData.CoarseLowerShape.Batch0006.a55.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0006.a55.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 9 := by decide +kernel
theorem ranks55_linked : ReferenceRankData.CoarseLowerShape.Batch0006.targetR55=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0006.targetA55=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 1 := by decide +kernel
theorem r_input55_linked : ReferenceRankData.CoarseLowerShape.Batch0006.r55.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds.gauge] := by decide +kernel
theorem a_input55_linked : ReferenceRankData.CoarseLowerShape.Batch0006.a55.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0006.a55.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0006.a55.bounds.gauge] := by decide +kernel
theorem geometry55_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.a := by decide +kernel
theorem weights110_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0013.cert110.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights111_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0013.cert111.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time55_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 10)=true := by decide +kernel
theorem r_reference55_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 0)=true := by decide +kernel
theorem a_reference55_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 1)=true := by decide +kernel
theorem rank_r_link55_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r55 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link55_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0006.a55.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a55 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints55 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell true ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds ReferenceRankData.CoarseLowerShape.Batch0006.r55 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile55_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link55_checked
    geometry55_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell false ReferenceProfileData.CoarseLowerShape.Batch0006.a55.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a55 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile55_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0006.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0006.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link55_checked
    geometry55_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks55_linked.1,←ranks55_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0006.r55.bounds ReferenceRankData.CoarseLowerShape.Batch0006.a55.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0006.ordered55_checked hr ha ho
theorem frozen_frame55 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55 ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds ReferenceProfileData.CoarseLowerShape.Batch0006.a55.bounds
  · rw [←r_profile55_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile55_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry55_linked.2.2.2.2.1
  · exact geometry55_linked.2.2.2.2.2
  · exact r_reference55_checked
  · exact a_reference55_checked
  · exact r_fixed55_linked
  · exact a_fixed55_linked
  · exact time55_checked
  · exact ht
  · exact hw
theorem child_geometry55_checked : ReferenceWeightData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights55 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0013.cert110∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch13_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0013.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0013.cert111∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch13_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0013.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry55_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights110_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry55_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry55_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights111_linked j (List.mem_finRange j))
theorem actual_frozen_frame55 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame55 (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.flow.timeParameter_mem child_geometry55_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights55 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell48),(ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell49),(ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell50),(ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell51),(ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell52),(ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell53),(ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell54),(ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0006.cell55)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0006.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0006.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame48 hz
  · exact fun z hz=>actual_frozen_frame49 hz
  · exact fun z hz=>actual_frozen_frame50 hz
  · exact fun z hz=>actual_frozen_frame51 hz
  · exact fun z hz=>actual_frozen_frame52 hz
  · exact fun z hz=>actual_frozen_frame53 hz
  · exact fun z hz=>actual_frozen_frame54 hz
  · exact fun z hz=>actual_frozen_frame55 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints48 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints49 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints50 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints51 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints52 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints53 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints54 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints55 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry48_linked.1,geometry48_linked.2.1,geometry48_linked.2.2.1,geometry48_linked.2.2.2.1⟩
  · exact ⟨geometry49_linked.1,geometry49_linked.2.1,geometry49_linked.2.2.1,geometry49_linked.2.2.2.1⟩
  · exact ⟨geometry50_linked.1,geometry50_linked.2.1,geometry50_linked.2.2.1,geometry50_linked.2.2.2.1⟩
  · exact ⟨geometry51_linked.1,geometry51_linked.2.1,geometry51_linked.2.2.1,geometry51_linked.2.2.2.1⟩
  · exact ⟨geometry52_linked.1,geometry52_linked.2.1,geometry52_linked.2.2.1,geometry52_linked.2.2.2.1⟩
  · exact ⟨geometry53_linked.1,geometry53_linked.2.1,geometry53_linked.2.2.1,geometry53_linked.2.2.2.1⟩
  · exact ⟨geometry54_linked.1,geometry54_linked.2.1,geometry54_linked.2.2.1,geometry54_linked.2.2.2.1⟩
  · exact ⟨geometry55_linked.1,geometry55_linked.2.1,geometry55_linked.2.2.1,geometry55_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.a48.bounds,?_,geometry48_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a48.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile48_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds,?_,geometry48_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert48.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r48.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile48_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.a49.bounds,?_,geometry49_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a49.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile49_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds,?_,geometry49_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert49.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r49.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile49_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.a50.bounds,?_,geometry50_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a50.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile50_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds,?_,geometry50_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert50.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r50.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile50_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.a51.bounds,?_,geometry51_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a51.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile51_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds,?_,geometry51_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert51.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r51.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile51_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.a52.bounds,?_,geometry52_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a52.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile52_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds,?_,geometry52_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert52.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r52.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile52_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.a53.bounds,?_,geometry53_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a53.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile53_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds,?_,geometry53_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert53.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r53.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile53_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.a54.bounds,?_,geometry54_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a54.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile54_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds,?_,geometry54_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert54.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r54.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile54_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.a55.bounds,?_,geometry55_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0006.a55.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile55_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds,?_,geometry55_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0006.cert55.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0006.r55.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile55_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0006.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0006.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0006
