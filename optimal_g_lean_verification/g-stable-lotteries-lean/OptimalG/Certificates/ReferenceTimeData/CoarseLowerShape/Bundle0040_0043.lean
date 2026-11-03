import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0037_0040
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0037_0040
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0081_0084
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0038_0041
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0039_0042
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Bundle0036_0039
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0041_0043
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0041_0043
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0085_0086
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0042_0043
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0043_0043

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0040
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch80_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0080.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0080.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch81_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0081.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0081.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile320_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r320=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds := by rfl
theorem a_profile320_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a320=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a320.bounds := by rfl
theorem r_fixed320_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 7 := by decide +kernel
theorem a_fixed320_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a320.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.a320.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 9 := by decide +kernel
theorem ranks320_linked : ReferenceRankData.CoarseLowerShape.Batch0040.targetR320=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0040.targetA320=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 1 := by decide +kernel
theorem r_input320_linked : ReferenceRankData.CoarseLowerShape.Batch0040.r320.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds.gauge] := by decide +kernel
theorem a_input320_linked : ReferenceRankData.CoarseLowerShape.Batch0040.a320.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.a320.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.a320.bounds.gauge] := by decide +kernel
theorem geometry320_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.a := by decide +kernel
theorem weights640_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0080.cert640.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights641_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0080.cert641.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time320_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 10)=true := by decide +kernel
theorem r_reference320_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 0)=true := by decide +kernel
theorem a_reference320_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 1)=true := by decide +kernel
theorem rank_r_link320_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r320 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link320_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0040.a320.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a320 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints320 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell true ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r320 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile320_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link320_checked
    geometry320_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell false ReferenceProfileData.CoarseLowerShape.Batch0040.a320.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a320 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile320_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link320_checked
    geometry320_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks320_linked.1,←ranks320_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0040.r320.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a320.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0040.ordered320_checked hr ha ho
theorem frozen_frame320 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320 ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds ReferenceProfileData.CoarseLowerShape.Batch0040.a320.bounds
  · rw [←r_profile320_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile320_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry320_linked.2.2.2.2.1
  · exact geometry320_linked.2.2.2.2.2
  · exact r_reference320_checked
  · exact a_reference320_checked
  · exact r_fixed320_linked
  · exact a_fixed320_linked
  · exact time320_checked
  · exact ht
  · exact hw
theorem child_geometry320_checked : ReferenceWeightData.CoarseLowerShape.Batch0080.cert640.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0080.cert640.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0080.cert641.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0080.cert641.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights320 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0080.cert640∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch80_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0080.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0080.cert641∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch80_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0080.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0080.cert640.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0080.cert640.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0080.cert640.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry320_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights640_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0080.cert641.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0080.cert641.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry320_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry320_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights641_linked j (List.mem_finRange j))
theorem actual_frozen_frame320 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame320 (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.flow.timeParameter_mem child_geometry320_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights320 hz)
theorem r_profile321_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r321=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds := by rfl
theorem a_profile321_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a321=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a321.bounds := by rfl
theorem r_fixed321_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 7 := by decide +kernel
theorem a_fixed321_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a321.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.a321.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 9 := by decide +kernel
theorem ranks321_linked : ReferenceRankData.CoarseLowerShape.Batch0040.targetR321=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0040.targetA321=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 1 := by decide +kernel
theorem r_input321_linked : ReferenceRankData.CoarseLowerShape.Batch0040.r321.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds.gauge] := by decide +kernel
theorem a_input321_linked : ReferenceRankData.CoarseLowerShape.Batch0040.a321.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.a321.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.a321.bounds.gauge] := by decide +kernel
theorem geometry321_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.a := by decide +kernel
theorem weights642_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0080.cert642.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights643_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0080.cert643.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time321_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 10)=true := by decide +kernel
theorem r_reference321_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 0)=true := by decide +kernel
theorem a_reference321_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 1)=true := by decide +kernel
theorem rank_r_link321_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r321 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link321_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0040.a321.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a321 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints321 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell true ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r321 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile321_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link321_checked
    geometry321_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell false ReferenceProfileData.CoarseLowerShape.Batch0040.a321.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a321 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile321_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link321_checked
    geometry321_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks321_linked.1,←ranks321_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0040.r321.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a321.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0040.ordered321_checked hr ha ho
theorem frozen_frame321 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321 ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds ReferenceProfileData.CoarseLowerShape.Batch0040.a321.bounds
  · rw [←r_profile321_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile321_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry321_linked.2.2.2.2.1
  · exact geometry321_linked.2.2.2.2.2
  · exact r_reference321_checked
  · exact a_reference321_checked
  · exact r_fixed321_linked
  · exact a_fixed321_linked
  · exact time321_checked
  · exact ht
  · exact hw
theorem child_geometry321_checked : ReferenceWeightData.CoarseLowerShape.Batch0080.cert642.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0080.cert642.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0080.cert643.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0080.cert643.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights321 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0080.cert642∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch80_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0080.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0080.cert643∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch80_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0080.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0080.cert642.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0080.cert642.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0080.cert642.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry321_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights642_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0080.cert643.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0080.cert643.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry321_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry321_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights643_linked j (List.mem_finRange j))
theorem actual_frozen_frame321 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame321 (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.flow.timeParameter_mem child_geometry321_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights321 hz)
theorem r_profile322_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r322=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds := by rfl
theorem a_profile322_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a322=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a322.bounds := by rfl
theorem r_fixed322_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 7 := by decide +kernel
theorem a_fixed322_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a322.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.a322.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 9 := by decide +kernel
theorem ranks322_linked : ReferenceRankData.CoarseLowerShape.Batch0040.targetR322=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0040.targetA322=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 1 := by decide +kernel
theorem r_input322_linked : ReferenceRankData.CoarseLowerShape.Batch0040.r322.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds.gauge] := by decide +kernel
theorem a_input322_linked : ReferenceRankData.CoarseLowerShape.Batch0040.a322.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.a322.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.a322.bounds.gauge] := by decide +kernel
theorem geometry322_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.a := by decide +kernel
theorem weights644_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0080.cert644.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights645_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0080.cert645.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time322_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 10)=true := by decide +kernel
theorem r_reference322_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 0)=true := by decide +kernel
theorem a_reference322_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 1)=true := by decide +kernel
theorem rank_r_link322_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r322 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link322_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0040.a322.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a322 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints322 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell true ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r322 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile322_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link322_checked
    geometry322_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell false ReferenceProfileData.CoarseLowerShape.Batch0040.a322.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a322 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile322_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link322_checked
    geometry322_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks322_linked.1,←ranks322_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0040.r322.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a322.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0040.ordered322_checked hr ha ho
theorem frozen_frame322 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322 ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds ReferenceProfileData.CoarseLowerShape.Batch0040.a322.bounds
  · rw [←r_profile322_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile322_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry322_linked.2.2.2.2.1
  · exact geometry322_linked.2.2.2.2.2
  · exact r_reference322_checked
  · exact a_reference322_checked
  · exact r_fixed322_linked
  · exact a_fixed322_linked
  · exact time322_checked
  · exact ht
  · exact hw
theorem child_geometry322_checked : ReferenceWeightData.CoarseLowerShape.Batch0080.cert644.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0080.cert644.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0080.cert645.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0080.cert645.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights322 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0080.cert644∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch80_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0080.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0080.cert645∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch80_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0080.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0080.cert644.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0080.cert644.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0080.cert644.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry322_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights644_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0080.cert645.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0080.cert645.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry322_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry322_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights645_linked j (List.mem_finRange j))
theorem actual_frozen_frame322 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame322 (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.flow.timeParameter_mem child_geometry322_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights322 hz)
theorem r_profile323_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r323=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds := by rfl
theorem a_profile323_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a323=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a323.bounds := by rfl
theorem r_fixed323_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 7 := by decide +kernel
theorem a_fixed323_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a323.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.a323.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 9 := by decide +kernel
theorem ranks323_linked : ReferenceRankData.CoarseLowerShape.Batch0040.targetR323=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0040.targetA323=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 1 := by decide +kernel
theorem r_input323_linked : ReferenceRankData.CoarseLowerShape.Batch0040.r323.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds.gauge] := by decide +kernel
theorem a_input323_linked : ReferenceRankData.CoarseLowerShape.Batch0040.a323.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.a323.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.a323.bounds.gauge] := by decide +kernel
theorem geometry323_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.a := by decide +kernel
theorem weights646_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0080.cert646.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights647_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0080.cert647.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time323_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 10)=true := by decide +kernel
theorem r_reference323_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 0)=true := by decide +kernel
theorem a_reference323_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 1)=true := by decide +kernel
theorem rank_r_link323_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r323 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link323_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0040.a323.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a323 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints323 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell true ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r323 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile323_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link323_checked
    geometry323_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell false ReferenceProfileData.CoarseLowerShape.Batch0040.a323.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a323 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile323_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link323_checked
    geometry323_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks323_linked.1,←ranks323_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0040.r323.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a323.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0040.ordered323_checked hr ha ho
theorem frozen_frame323 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323 ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds ReferenceProfileData.CoarseLowerShape.Batch0040.a323.bounds
  · rw [←r_profile323_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile323_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry323_linked.2.2.2.2.1
  · exact geometry323_linked.2.2.2.2.2
  · exact r_reference323_checked
  · exact a_reference323_checked
  · exact r_fixed323_linked
  · exact a_fixed323_linked
  · exact time323_checked
  · exact ht
  · exact hw
theorem child_geometry323_checked : ReferenceWeightData.CoarseLowerShape.Batch0080.cert646.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0080.cert646.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0080.cert647.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0080.cert647.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights323 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0080.cert646∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch80_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0080.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0080.cert647∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch80_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0080.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0080.cert646.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0080.cert646.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0080.cert646.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry323_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights646_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0080.cert647.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0080.cert647.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry323_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry323_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights647_linked j (List.mem_finRange j))
theorem actual_frozen_frame323 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame323 (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.flow.timeParameter_mem child_geometry323_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights323 hz)
theorem r_profile324_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r324=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds := by rfl
theorem a_profile324_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a324=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a324.bounds := by rfl
theorem r_fixed324_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 7 := by decide +kernel
theorem a_fixed324_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a324.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.a324.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 9 := by decide +kernel
theorem ranks324_linked : ReferenceRankData.CoarseLowerShape.Batch0040.targetR324=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0040.targetA324=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 1 := by decide +kernel
theorem r_input324_linked : ReferenceRankData.CoarseLowerShape.Batch0040.r324.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds.gauge] := by decide +kernel
theorem a_input324_linked : ReferenceRankData.CoarseLowerShape.Batch0040.a324.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.a324.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.a324.bounds.gauge] := by decide +kernel
theorem geometry324_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.a := by decide +kernel
theorem weights648_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0081.cert648.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights649_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0081.cert649.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time324_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 10)=true := by decide +kernel
theorem r_reference324_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 0)=true := by decide +kernel
theorem a_reference324_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 1)=true := by decide +kernel
theorem rank_r_link324_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r324 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link324_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0040.a324.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a324 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints324 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell true ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r324 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile324_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link324_checked
    geometry324_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell false ReferenceProfileData.CoarseLowerShape.Batch0040.a324.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a324 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile324_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link324_checked
    geometry324_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks324_linked.1,←ranks324_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0040.r324.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a324.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0040.ordered324_checked hr ha ho
theorem frozen_frame324 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324 ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds ReferenceProfileData.CoarseLowerShape.Batch0040.a324.bounds
  · rw [←r_profile324_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile324_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry324_linked.2.2.2.2.1
  · exact geometry324_linked.2.2.2.2.2
  · exact r_reference324_checked
  · exact a_reference324_checked
  · exact r_fixed324_linked
  · exact a_fixed324_linked
  · exact time324_checked
  · exact ht
  · exact hw
theorem child_geometry324_checked : ReferenceWeightData.CoarseLowerShape.Batch0081.cert648.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0081.cert648.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0081.cert649.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0081.cert649.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights324 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0081.cert648∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch81_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0081.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0081.cert649∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch81_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0081.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0081.cert648.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0081.cert648.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0081.cert648.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry324_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights648_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0081.cert649.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0081.cert649.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry324_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry324_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights649_linked j (List.mem_finRange j))
theorem actual_frozen_frame324 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame324 (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.flow.timeParameter_mem child_geometry324_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights324 hz)
theorem r_profile325_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r325=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds := by rfl
theorem a_profile325_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a325=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a325.bounds := by rfl
theorem r_fixed325_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 7 := by decide +kernel
theorem a_fixed325_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a325.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.a325.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 9 := by decide +kernel
theorem ranks325_linked : ReferenceRankData.CoarseLowerShape.Batch0040.targetR325=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0040.targetA325=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 1 := by decide +kernel
theorem r_input325_linked : ReferenceRankData.CoarseLowerShape.Batch0040.r325.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds.gauge] := by decide +kernel
theorem a_input325_linked : ReferenceRankData.CoarseLowerShape.Batch0040.a325.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.a325.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.a325.bounds.gauge] := by decide +kernel
theorem geometry325_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.a := by decide +kernel
theorem weights650_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0081.cert650.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights651_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0081.cert651.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time325_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 10)=true := by decide +kernel
theorem r_reference325_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 0)=true := by decide +kernel
theorem a_reference325_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 1)=true := by decide +kernel
theorem rank_r_link325_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r325 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link325_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0040.a325.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a325 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints325 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell true ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r325 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile325_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link325_checked
    geometry325_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell false ReferenceProfileData.CoarseLowerShape.Batch0040.a325.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a325 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile325_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link325_checked
    geometry325_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks325_linked.1,←ranks325_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0040.r325.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a325.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0040.ordered325_checked hr ha ho
theorem frozen_frame325 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325 ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds ReferenceProfileData.CoarseLowerShape.Batch0040.a325.bounds
  · rw [←r_profile325_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile325_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry325_linked.2.2.2.2.1
  · exact geometry325_linked.2.2.2.2.2
  · exact r_reference325_checked
  · exact a_reference325_checked
  · exact r_fixed325_linked
  · exact a_fixed325_linked
  · exact time325_checked
  · exact ht
  · exact hw
theorem child_geometry325_checked : ReferenceWeightData.CoarseLowerShape.Batch0081.cert650.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0081.cert650.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0081.cert651.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0081.cert651.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights325 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0081.cert650∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch81_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0081.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0081.cert651∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch81_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0081.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0081.cert650.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0081.cert650.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0081.cert650.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry325_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights650_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0081.cert651.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0081.cert651.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry325_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry325_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights651_linked j (List.mem_finRange j))
theorem actual_frozen_frame325 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame325 (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.flow.timeParameter_mem child_geometry325_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights325 hz)
theorem r_profile326_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r326=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds := by rfl
theorem a_profile326_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a326=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a326.bounds := by rfl
theorem r_fixed326_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 7 := by decide +kernel
theorem a_fixed326_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a326.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.a326.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 9 := by decide +kernel
theorem ranks326_linked : ReferenceRankData.CoarseLowerShape.Batch0040.targetR326=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0040.targetA326=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 1 := by decide +kernel
theorem r_input326_linked : ReferenceRankData.CoarseLowerShape.Batch0040.r326.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds.gauge] := by decide +kernel
theorem a_input326_linked : ReferenceRankData.CoarseLowerShape.Batch0040.a326.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.a326.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.a326.bounds.gauge] := by decide +kernel
theorem geometry326_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.a := by decide +kernel
theorem weights652_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0081.cert652.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights653_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0081.cert653.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time326_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 10)=true := by decide +kernel
theorem r_reference326_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 0)=true := by decide +kernel
theorem a_reference326_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 1)=true := by decide +kernel
theorem rank_r_link326_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r326 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link326_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0040.a326.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a326 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints326 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell true ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r326 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile326_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link326_checked
    geometry326_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell false ReferenceProfileData.CoarseLowerShape.Batch0040.a326.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a326 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile326_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link326_checked
    geometry326_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks326_linked.1,←ranks326_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0040.r326.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a326.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0040.ordered326_checked hr ha ho
theorem frozen_frame326 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326 ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds ReferenceProfileData.CoarseLowerShape.Batch0040.a326.bounds
  · rw [←r_profile326_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile326_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry326_linked.2.2.2.2.1
  · exact geometry326_linked.2.2.2.2.2
  · exact r_reference326_checked
  · exact a_reference326_checked
  · exact r_fixed326_linked
  · exact a_fixed326_linked
  · exact time326_checked
  · exact ht
  · exact hw
theorem child_geometry326_checked : ReferenceWeightData.CoarseLowerShape.Batch0081.cert652.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0081.cert652.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0081.cert653.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0081.cert653.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights326 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0081.cert652∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch81_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0081.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0081.cert653∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch81_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0081.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0081.cert652.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0081.cert652.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0081.cert652.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry326_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights652_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0081.cert653.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0081.cert653.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry326_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry326_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights653_linked j (List.mem_finRange j))
theorem actual_frozen_frame326 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame326 (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.flow.timeParameter_mem child_geometry326_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights326 hz)
theorem r_profile327_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r327=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds := by rfl
theorem a_profile327_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a327=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a327.bounds := by rfl
theorem r_fixed327_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 7 := by decide +kernel
theorem a_fixed327_linked : ReferenceProfileData.CoarseLowerShape.Batch0040.a327.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0040.a327.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 9 := by decide +kernel
theorem ranks327_linked : ReferenceRankData.CoarseLowerShape.Batch0040.targetR327=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0040.targetA327=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 1 := by decide +kernel
theorem r_input327_linked : ReferenceRankData.CoarseLowerShape.Batch0040.r327.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds.gauge] := by decide +kernel
theorem a_input327_linked : ReferenceRankData.CoarseLowerShape.Batch0040.a327.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0040.a327.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0040.a327.bounds.gauge] := by decide +kernel
theorem geometry327_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.a := by decide +kernel
theorem weights654_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0081.cert654.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights655_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0081.cert655.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time327_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 10)=true := by decide +kernel
theorem r_reference327_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 0)=true := by decide +kernel
theorem a_reference327_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 1)=true := by decide +kernel
theorem rank_r_link327_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r327 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link327_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0040.a327.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a327 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints327 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell true ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds ReferenceRankData.CoarseLowerShape.Batch0040.r327 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile327_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link327_checked
    geometry327_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell false ReferenceProfileData.CoarseLowerShape.Batch0040.a327.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a327 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile327_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0040.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0040.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link327_checked
    geometry327_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks327_linked.1,←ranks327_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0040.r327.bounds ReferenceRankData.CoarseLowerShape.Batch0040.a327.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0040.ordered327_checked hr ha ho
theorem frozen_frame327 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327 ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds ReferenceProfileData.CoarseLowerShape.Batch0040.a327.bounds
  · rw [←r_profile327_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile327_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry327_linked.2.2.2.2.1
  · exact geometry327_linked.2.2.2.2.2
  · exact r_reference327_checked
  · exact a_reference327_checked
  · exact r_fixed327_linked
  · exact a_fixed327_linked
  · exact time327_checked
  · exact ht
  · exact hw
theorem child_geometry327_checked : ReferenceWeightData.CoarseLowerShape.Batch0081.cert654.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0081.cert654.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0081.cert655.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0081.cert655.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights327 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0081.cert654∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch81_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0081.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0081.cert655∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch81_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0081.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0081.cert654.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0081.cert654.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0081.cert654.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry327_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights654_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0081.cert655.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0081.cert655.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry327_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry327_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights655_linked j (List.mem_finRange j))
theorem actual_frozen_frame327 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame327 (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.flow.timeParameter_mem child_geometry327_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights327 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell320),(ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell321),(ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell322),(ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell323),(ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell324),(ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell325),(ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell326),(ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0040.cell327)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0040.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0040.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame320 hz
  · exact fun z hz=>actual_frozen_frame321 hz
  · exact fun z hz=>actual_frozen_frame322 hz
  · exact fun z hz=>actual_frozen_frame323 hz
  · exact fun z hz=>actual_frozen_frame324 hz
  · exact fun z hz=>actual_frozen_frame325 hz
  · exact fun z hz=>actual_frozen_frame326 hz
  · exact fun z hz=>actual_frozen_frame327 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints320 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints321 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints322 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints323 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints324 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints325 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints326 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints327 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry320_linked.1,geometry320_linked.2.1,geometry320_linked.2.2.1,geometry320_linked.2.2.2.1⟩
  · exact ⟨geometry321_linked.1,geometry321_linked.2.1,geometry321_linked.2.2.1,geometry321_linked.2.2.2.1⟩
  · exact ⟨geometry322_linked.1,geometry322_linked.2.1,geometry322_linked.2.2.1,geometry322_linked.2.2.2.1⟩
  · exact ⟨geometry323_linked.1,geometry323_linked.2.1,geometry323_linked.2.2.1,geometry323_linked.2.2.2.1⟩
  · exact ⟨geometry324_linked.1,geometry324_linked.2.1,geometry324_linked.2.2.1,geometry324_linked.2.2.2.1⟩
  · exact ⟨geometry325_linked.1,geometry325_linked.2.1,geometry325_linked.2.2.1,geometry325_linked.2.2.2.1⟩
  · exact ⟨geometry326_linked.1,geometry326_linked.2.1,geometry326_linked.2.2.1,geometry326_linked.2.2.2.1⟩
  · exact ⟨geometry327_linked.1,geometry327_linked.2.1,geometry327_linked.2.2.1,geometry327_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.a320.bounds,?_,geometry320_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a320.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile320_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds,?_,geometry320_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert320.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r320.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile320_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.a321.bounds,?_,geometry321_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a321.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile321_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds,?_,geometry321_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert321.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r321.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile321_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.a322.bounds,?_,geometry322_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a322.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile322_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds,?_,geometry322_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert322.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r322.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile322_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.a323.bounds,?_,geometry323_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a323.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile323_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds,?_,geometry323_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert323.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r323.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile323_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.a324.bounds,?_,geometry324_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a324.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile324_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds,?_,geometry324_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert324.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r324.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile324_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.a325.bounds,?_,geometry325_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a325.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile325_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds,?_,geometry325_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert325.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r325.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile325_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.a326.bounds,?_,geometry326_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a326.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile326_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds,?_,geometry326_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert326.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r326.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile326_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.a327.bounds,?_,geometry327_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0040.a327.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile327_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds,?_,geometry327_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0040.cert327.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0040.r327.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile327_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0040.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0040.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0040

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0041
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch82_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0082.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0082.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch83_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0083.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0083.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile328_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r328=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds := by rfl
theorem a_profile328_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a328=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a328.bounds := by rfl
theorem r_fixed328_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 7 := by decide +kernel
theorem a_fixed328_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a328.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.a328.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 9 := by decide +kernel
theorem ranks328_linked : ReferenceRankData.CoarseLowerShape.Batch0041.targetR328=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0041.targetA328=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 1 := by decide +kernel
theorem r_input328_linked : ReferenceRankData.CoarseLowerShape.Batch0041.r328.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds.gauge] := by decide +kernel
theorem a_input328_linked : ReferenceRankData.CoarseLowerShape.Batch0041.a328.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.a328.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.a328.bounds.gauge] := by decide +kernel
theorem geometry328_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.a := by decide +kernel
theorem weights656_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0082.cert656.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights657_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0082.cert657.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time328_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 10)=true := by decide +kernel
theorem r_reference328_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 0)=true := by decide +kernel
theorem a_reference328_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 1)=true := by decide +kernel
theorem rank_r_link328_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r328 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link328_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0041.a328.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a328 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints328 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell true ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r328 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile328_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link328_checked
    geometry328_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell false ReferenceProfileData.CoarseLowerShape.Batch0041.a328.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a328 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile328_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link328_checked
    geometry328_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks328_linked.1,←ranks328_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0041.r328.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a328.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0041.ordered328_checked hr ha ho
theorem frozen_frame328 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328 ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds ReferenceProfileData.CoarseLowerShape.Batch0041.a328.bounds
  · rw [←r_profile328_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile328_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry328_linked.2.2.2.2.1
  · exact geometry328_linked.2.2.2.2.2
  · exact r_reference328_checked
  · exact a_reference328_checked
  · exact r_fixed328_linked
  · exact a_fixed328_linked
  · exact time328_checked
  · exact ht
  · exact hw
theorem child_geometry328_checked : ReferenceWeightData.CoarseLowerShape.Batch0082.cert656.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0082.cert656.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0082.cert657.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0082.cert657.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights328 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0082.cert656∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch82_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0082.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0082.cert657∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch82_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0082.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0082.cert656.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0082.cert656.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0082.cert656.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry328_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights656_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0082.cert657.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0082.cert657.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry328_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry328_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights657_linked j (List.mem_finRange j))
theorem actual_frozen_frame328 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame328 (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.flow.timeParameter_mem child_geometry328_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights328 hz)
theorem r_profile329_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r329=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds := by rfl
theorem a_profile329_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a329=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a329.bounds := by rfl
theorem r_fixed329_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 7 := by decide +kernel
theorem a_fixed329_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a329.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.a329.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 9 := by decide +kernel
theorem ranks329_linked : ReferenceRankData.CoarseLowerShape.Batch0041.targetR329=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0041.targetA329=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 1 := by decide +kernel
theorem r_input329_linked : ReferenceRankData.CoarseLowerShape.Batch0041.r329.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds.gauge] := by decide +kernel
theorem a_input329_linked : ReferenceRankData.CoarseLowerShape.Batch0041.a329.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.a329.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.a329.bounds.gauge] := by decide +kernel
theorem geometry329_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.a := by decide +kernel
theorem weights658_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0082.cert658.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights659_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0082.cert659.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time329_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 10)=true := by decide +kernel
theorem r_reference329_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 0)=true := by decide +kernel
theorem a_reference329_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 1)=true := by decide +kernel
theorem rank_r_link329_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r329 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link329_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0041.a329.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a329 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints329 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell true ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r329 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile329_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link329_checked
    geometry329_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell false ReferenceProfileData.CoarseLowerShape.Batch0041.a329.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a329 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile329_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link329_checked
    geometry329_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks329_linked.1,←ranks329_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0041.r329.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a329.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0041.ordered329_checked hr ha ho
theorem frozen_frame329 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329 ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds ReferenceProfileData.CoarseLowerShape.Batch0041.a329.bounds
  · rw [←r_profile329_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile329_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry329_linked.2.2.2.2.1
  · exact geometry329_linked.2.2.2.2.2
  · exact r_reference329_checked
  · exact a_reference329_checked
  · exact r_fixed329_linked
  · exact a_fixed329_linked
  · exact time329_checked
  · exact ht
  · exact hw
theorem child_geometry329_checked : ReferenceWeightData.CoarseLowerShape.Batch0082.cert658.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0082.cert658.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0082.cert659.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0082.cert659.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights329 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0082.cert658∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch82_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0082.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0082.cert659∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch82_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0082.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0082.cert658.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0082.cert658.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0082.cert658.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry329_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights658_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0082.cert659.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0082.cert659.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry329_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry329_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights659_linked j (List.mem_finRange j))
theorem actual_frozen_frame329 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame329 (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.flow.timeParameter_mem child_geometry329_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights329 hz)
theorem r_profile330_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r330=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds := by rfl
theorem a_profile330_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a330=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a330.bounds := by rfl
theorem r_fixed330_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 7 := by decide +kernel
theorem a_fixed330_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a330.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.a330.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 9 := by decide +kernel
theorem ranks330_linked : ReferenceRankData.CoarseLowerShape.Batch0041.targetR330=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0041.targetA330=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 1 := by decide +kernel
theorem r_input330_linked : ReferenceRankData.CoarseLowerShape.Batch0041.r330.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds.gauge] := by decide +kernel
theorem a_input330_linked : ReferenceRankData.CoarseLowerShape.Batch0041.a330.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.a330.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.a330.bounds.gauge] := by decide +kernel
theorem geometry330_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.a := by decide +kernel
theorem weights660_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0082.cert660.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights661_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0082.cert661.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time330_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 10)=true := by decide +kernel
theorem r_reference330_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 0)=true := by decide +kernel
theorem a_reference330_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 1)=true := by decide +kernel
theorem rank_r_link330_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r330 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link330_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0041.a330.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a330 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints330 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell true ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r330 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile330_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link330_checked
    geometry330_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell false ReferenceProfileData.CoarseLowerShape.Batch0041.a330.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a330 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile330_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link330_checked
    geometry330_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks330_linked.1,←ranks330_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0041.r330.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a330.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0041.ordered330_checked hr ha ho
theorem frozen_frame330 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330 ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds ReferenceProfileData.CoarseLowerShape.Batch0041.a330.bounds
  · rw [←r_profile330_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile330_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry330_linked.2.2.2.2.1
  · exact geometry330_linked.2.2.2.2.2
  · exact r_reference330_checked
  · exact a_reference330_checked
  · exact r_fixed330_linked
  · exact a_fixed330_linked
  · exact time330_checked
  · exact ht
  · exact hw
theorem child_geometry330_checked : ReferenceWeightData.CoarseLowerShape.Batch0082.cert660.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0082.cert660.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0082.cert661.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0082.cert661.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights330 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0082.cert660∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch82_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0082.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0082.cert661∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch82_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0082.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0082.cert660.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0082.cert660.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0082.cert660.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry330_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights660_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0082.cert661.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0082.cert661.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry330_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry330_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights661_linked j (List.mem_finRange j))
theorem actual_frozen_frame330 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame330 (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.flow.timeParameter_mem child_geometry330_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights330 hz)
theorem r_profile331_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r331=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds := by rfl
theorem a_profile331_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a331=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a331.bounds := by rfl
theorem r_fixed331_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 7 := by decide +kernel
theorem a_fixed331_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a331.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.a331.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 9 := by decide +kernel
theorem ranks331_linked : ReferenceRankData.CoarseLowerShape.Batch0041.targetR331=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0041.targetA331=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 1 := by decide +kernel
theorem r_input331_linked : ReferenceRankData.CoarseLowerShape.Batch0041.r331.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds.gauge] := by decide +kernel
theorem a_input331_linked : ReferenceRankData.CoarseLowerShape.Batch0041.a331.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.a331.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.a331.bounds.gauge] := by decide +kernel
theorem geometry331_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.a := by decide +kernel
theorem weights662_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0082.cert662.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights663_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0082.cert663.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time331_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 10)=true := by decide +kernel
theorem r_reference331_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 0)=true := by decide +kernel
theorem a_reference331_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 1)=true := by decide +kernel
theorem rank_r_link331_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r331 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link331_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0041.a331.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a331 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints331 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell true ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r331 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile331_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link331_checked
    geometry331_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell false ReferenceProfileData.CoarseLowerShape.Batch0041.a331.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a331 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile331_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link331_checked
    geometry331_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks331_linked.1,←ranks331_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0041.r331.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a331.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0041.ordered331_checked hr ha ho
theorem frozen_frame331 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331 ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds ReferenceProfileData.CoarseLowerShape.Batch0041.a331.bounds
  · rw [←r_profile331_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile331_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry331_linked.2.2.2.2.1
  · exact geometry331_linked.2.2.2.2.2
  · exact r_reference331_checked
  · exact a_reference331_checked
  · exact r_fixed331_linked
  · exact a_fixed331_linked
  · exact time331_checked
  · exact ht
  · exact hw
theorem child_geometry331_checked : ReferenceWeightData.CoarseLowerShape.Batch0082.cert662.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0082.cert662.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0082.cert663.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0082.cert663.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights331 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0082.cert662∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch82_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0082.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0082.cert663∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch82_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0082.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0082.cert662.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0082.cert662.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0082.cert662.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry331_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights662_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0082.cert663.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0082.cert663.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry331_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry331_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights663_linked j (List.mem_finRange j))
theorem actual_frozen_frame331 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame331 (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.flow.timeParameter_mem child_geometry331_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights331 hz)
theorem r_profile332_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r332=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds := by rfl
theorem a_profile332_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a332=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a332.bounds := by rfl
theorem r_fixed332_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 7 := by decide +kernel
theorem a_fixed332_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a332.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.a332.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 9 := by decide +kernel
theorem ranks332_linked : ReferenceRankData.CoarseLowerShape.Batch0041.targetR332=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0041.targetA332=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 1 := by decide +kernel
theorem r_input332_linked : ReferenceRankData.CoarseLowerShape.Batch0041.r332.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds.gauge] := by decide +kernel
theorem a_input332_linked : ReferenceRankData.CoarseLowerShape.Batch0041.a332.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.a332.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.a332.bounds.gauge] := by decide +kernel
theorem geometry332_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.a := by decide +kernel
theorem weights664_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0083.cert664.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights665_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0083.cert665.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time332_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 10)=true := by decide +kernel
theorem r_reference332_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 0)=true := by decide +kernel
theorem a_reference332_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 1)=true := by decide +kernel
theorem rank_r_link332_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r332 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link332_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0041.a332.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a332 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints332 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell true ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r332 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile332_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link332_checked
    geometry332_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell false ReferenceProfileData.CoarseLowerShape.Batch0041.a332.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a332 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile332_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link332_checked
    geometry332_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks332_linked.1,←ranks332_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0041.r332.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a332.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0041.ordered332_checked hr ha ho
theorem frozen_frame332 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332 ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds ReferenceProfileData.CoarseLowerShape.Batch0041.a332.bounds
  · rw [←r_profile332_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile332_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry332_linked.2.2.2.2.1
  · exact geometry332_linked.2.2.2.2.2
  · exact r_reference332_checked
  · exact a_reference332_checked
  · exact r_fixed332_linked
  · exact a_fixed332_linked
  · exact time332_checked
  · exact ht
  · exact hw
theorem child_geometry332_checked : ReferenceWeightData.CoarseLowerShape.Batch0083.cert664.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0083.cert664.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0083.cert665.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0083.cert665.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights332 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0083.cert664∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch83_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0083.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0083.cert665∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch83_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0083.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0083.cert664.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0083.cert664.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0083.cert664.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry332_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights664_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0083.cert665.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0083.cert665.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry332_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry332_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights665_linked j (List.mem_finRange j))
theorem actual_frozen_frame332 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame332 (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.flow.timeParameter_mem child_geometry332_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights332 hz)
theorem r_profile333_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r333=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds := by rfl
theorem a_profile333_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a333=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a333.bounds := by rfl
theorem r_fixed333_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 7 := by decide +kernel
theorem a_fixed333_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a333.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.a333.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 9 := by decide +kernel
theorem ranks333_linked : ReferenceRankData.CoarseLowerShape.Batch0041.targetR333=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0041.targetA333=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 1 := by decide +kernel
theorem r_input333_linked : ReferenceRankData.CoarseLowerShape.Batch0041.r333.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds.gauge] := by decide +kernel
theorem a_input333_linked : ReferenceRankData.CoarseLowerShape.Batch0041.a333.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.a333.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.a333.bounds.gauge] := by decide +kernel
theorem geometry333_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.a := by decide +kernel
theorem weights666_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0083.cert666.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights667_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0083.cert667.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time333_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 10)=true := by decide +kernel
theorem r_reference333_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 0)=true := by decide +kernel
theorem a_reference333_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 1)=true := by decide +kernel
theorem rank_r_link333_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r333 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link333_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0041.a333.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a333 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints333 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell true ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r333 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile333_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link333_checked
    geometry333_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell false ReferenceProfileData.CoarseLowerShape.Batch0041.a333.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a333 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile333_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link333_checked
    geometry333_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks333_linked.1,←ranks333_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0041.r333.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a333.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0041.ordered333_checked hr ha ho
theorem frozen_frame333 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333 ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds ReferenceProfileData.CoarseLowerShape.Batch0041.a333.bounds
  · rw [←r_profile333_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile333_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry333_linked.2.2.2.2.1
  · exact geometry333_linked.2.2.2.2.2
  · exact r_reference333_checked
  · exact a_reference333_checked
  · exact r_fixed333_linked
  · exact a_fixed333_linked
  · exact time333_checked
  · exact ht
  · exact hw
theorem child_geometry333_checked : ReferenceWeightData.CoarseLowerShape.Batch0083.cert666.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0083.cert666.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0083.cert667.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0083.cert667.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights333 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0083.cert666∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch83_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0083.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0083.cert667∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch83_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0083.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0083.cert666.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0083.cert666.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0083.cert666.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry333_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights666_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0083.cert667.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0083.cert667.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry333_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry333_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights667_linked j (List.mem_finRange j))
theorem actual_frozen_frame333 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame333 (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.flow.timeParameter_mem child_geometry333_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights333 hz)
theorem r_profile334_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r334=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds := by rfl
theorem a_profile334_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a334=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a334.bounds := by rfl
theorem r_fixed334_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 7 := by decide +kernel
theorem a_fixed334_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a334.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.a334.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 9 := by decide +kernel
theorem ranks334_linked : ReferenceRankData.CoarseLowerShape.Batch0041.targetR334=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0041.targetA334=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 1 := by decide +kernel
theorem r_input334_linked : ReferenceRankData.CoarseLowerShape.Batch0041.r334.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds.gauge] := by decide +kernel
theorem a_input334_linked : ReferenceRankData.CoarseLowerShape.Batch0041.a334.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.a334.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.a334.bounds.gauge] := by decide +kernel
theorem geometry334_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.a := by decide +kernel
theorem weights668_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0083.cert668.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights669_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0083.cert669.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time334_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 10)=true := by decide +kernel
theorem r_reference334_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 0)=true := by decide +kernel
theorem a_reference334_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 1)=true := by decide +kernel
theorem rank_r_link334_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r334 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link334_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0041.a334.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a334 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints334 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell true ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r334 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile334_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link334_checked
    geometry334_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell false ReferenceProfileData.CoarseLowerShape.Batch0041.a334.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a334 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile334_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link334_checked
    geometry334_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks334_linked.1,←ranks334_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0041.r334.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a334.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0041.ordered334_checked hr ha ho
theorem frozen_frame334 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334 ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds ReferenceProfileData.CoarseLowerShape.Batch0041.a334.bounds
  · rw [←r_profile334_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile334_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry334_linked.2.2.2.2.1
  · exact geometry334_linked.2.2.2.2.2
  · exact r_reference334_checked
  · exact a_reference334_checked
  · exact r_fixed334_linked
  · exact a_fixed334_linked
  · exact time334_checked
  · exact ht
  · exact hw
theorem child_geometry334_checked : ReferenceWeightData.CoarseLowerShape.Batch0083.cert668.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0083.cert668.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0083.cert669.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0083.cert669.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights334 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0083.cert668∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch83_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0083.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0083.cert669∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch83_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0083.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0083.cert668.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0083.cert668.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0083.cert668.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry334_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights668_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0083.cert669.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0083.cert669.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry334_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry334_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights669_linked j (List.mem_finRange j))
theorem actual_frozen_frame334 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame334 (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.flow.timeParameter_mem child_geometry334_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights334 hz)
theorem r_profile335_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r335=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds := by rfl
theorem a_profile335_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a335=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a335.bounds := by rfl
theorem r_fixed335_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 7 := by decide +kernel
theorem a_fixed335_linked : ReferenceProfileData.CoarseLowerShape.Batch0041.a335.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0041.a335.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 9 := by decide +kernel
theorem ranks335_linked : ReferenceRankData.CoarseLowerShape.Batch0041.targetR335=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0041.targetA335=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 1 := by decide +kernel
theorem r_input335_linked : ReferenceRankData.CoarseLowerShape.Batch0041.r335.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds.gauge] := by decide +kernel
theorem a_input335_linked : ReferenceRankData.CoarseLowerShape.Batch0041.a335.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0041.a335.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0041.a335.bounds.gauge] := by decide +kernel
theorem geometry335_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.a := by decide +kernel
theorem weights670_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0083.cert670.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights671_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0083.cert671.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time335_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 10)=true := by decide +kernel
theorem r_reference335_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 0)=true := by decide +kernel
theorem a_reference335_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 1)=true := by decide +kernel
theorem rank_r_link335_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r335 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link335_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0041.a335.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a335 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints335 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell true ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds ReferenceRankData.CoarseLowerShape.Batch0041.r335 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile335_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link335_checked
    geometry335_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell false ReferenceProfileData.CoarseLowerShape.Batch0041.a335.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a335 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile335_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0041.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0041.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link335_checked
    geometry335_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks335_linked.1,←ranks335_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0041.r335.bounds ReferenceRankData.CoarseLowerShape.Batch0041.a335.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0041.ordered335_checked hr ha ho
theorem frozen_frame335 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335 ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds ReferenceProfileData.CoarseLowerShape.Batch0041.a335.bounds
  · rw [←r_profile335_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile335_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry335_linked.2.2.2.2.1
  · exact geometry335_linked.2.2.2.2.2
  · exact r_reference335_checked
  · exact a_reference335_checked
  · exact r_fixed335_linked
  · exact a_fixed335_linked
  · exact time335_checked
  · exact ht
  · exact hw
theorem child_geometry335_checked : ReferenceWeightData.CoarseLowerShape.Batch0083.cert670.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0083.cert670.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0083.cert671.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0083.cert671.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights335 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0083.cert670∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch83_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0083.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0083.cert671∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch83_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0083.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0083.cert670.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0083.cert670.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0083.cert670.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry335_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights670_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0083.cert671.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0083.cert671.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry335_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry335_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights671_linked j (List.mem_finRange j))
theorem actual_frozen_frame335 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame335 (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.flow.timeParameter_mem child_geometry335_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights335 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell328),(ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell329),(ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell330),(ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell331),(ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell332),(ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell333),(ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell334),(ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0041.cell335)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0041.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0041.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame328 hz
  · exact fun z hz=>actual_frozen_frame329 hz
  · exact fun z hz=>actual_frozen_frame330 hz
  · exact fun z hz=>actual_frozen_frame331 hz
  · exact fun z hz=>actual_frozen_frame332 hz
  · exact fun z hz=>actual_frozen_frame333 hz
  · exact fun z hz=>actual_frozen_frame334 hz
  · exact fun z hz=>actual_frozen_frame335 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints328 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints329 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints330 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints331 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints332 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints333 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints334 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints335 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry328_linked.1,geometry328_linked.2.1,geometry328_linked.2.2.1,geometry328_linked.2.2.2.1⟩
  · exact ⟨geometry329_linked.1,geometry329_linked.2.1,geometry329_linked.2.2.1,geometry329_linked.2.2.2.1⟩
  · exact ⟨geometry330_linked.1,geometry330_linked.2.1,geometry330_linked.2.2.1,geometry330_linked.2.2.2.1⟩
  · exact ⟨geometry331_linked.1,geometry331_linked.2.1,geometry331_linked.2.2.1,geometry331_linked.2.2.2.1⟩
  · exact ⟨geometry332_linked.1,geometry332_linked.2.1,geometry332_linked.2.2.1,geometry332_linked.2.2.2.1⟩
  · exact ⟨geometry333_linked.1,geometry333_linked.2.1,geometry333_linked.2.2.1,geometry333_linked.2.2.2.1⟩
  · exact ⟨geometry334_linked.1,geometry334_linked.2.1,geometry334_linked.2.2.1,geometry334_linked.2.2.2.1⟩
  · exact ⟨geometry335_linked.1,geometry335_linked.2.1,geometry335_linked.2.2.1,geometry335_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.a328.bounds,?_,geometry328_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a328.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile328_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds,?_,geometry328_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert328.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r328.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile328_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.a329.bounds,?_,geometry329_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a329.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile329_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds,?_,geometry329_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert329.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r329.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile329_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.a330.bounds,?_,geometry330_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a330.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile330_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds,?_,geometry330_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert330.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r330.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile330_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.a331.bounds,?_,geometry331_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a331.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile331_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds,?_,geometry331_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert331.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r331.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile331_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.a332.bounds,?_,geometry332_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a332.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile332_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds,?_,geometry332_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert332.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r332.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile332_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.a333.bounds,?_,geometry333_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a333.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile333_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds,?_,geometry333_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert333.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r333.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile333_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.a334.bounds,?_,geometry334_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a334.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile334_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds,?_,geometry334_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert334.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r334.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile334_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.a335.bounds,?_,geometry335_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0041.a335.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile335_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds,?_,geometry335_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0041.cert335.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0041.r335.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile335_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0041.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0041.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0041

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0042
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch84_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0084.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0084.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch85_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0085.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0085.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile336_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r336=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds := by rfl
theorem a_profile336_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a336=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a336.bounds := by rfl
theorem r_fixed336_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 7 := by decide +kernel
theorem a_fixed336_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a336.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.a336.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 9 := by decide +kernel
theorem ranks336_linked : ReferenceRankData.CoarseLowerShape.Batch0042.targetR336=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0042.targetA336=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 1 := by decide +kernel
theorem r_input336_linked : ReferenceRankData.CoarseLowerShape.Batch0042.r336.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds.gauge] := by decide +kernel
theorem a_input336_linked : ReferenceRankData.CoarseLowerShape.Batch0042.a336.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.a336.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.a336.bounds.gauge] := by decide +kernel
theorem geometry336_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.a := by decide +kernel
theorem weights672_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0084.cert672.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights673_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0084.cert673.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time336_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 10)=true := by decide +kernel
theorem r_reference336_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 0)=true := by decide +kernel
theorem a_reference336_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 1)=true := by decide +kernel
theorem rank_r_link336_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r336 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link336_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0042.a336.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a336 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints336 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell true ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r336 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile336_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link336_checked
    geometry336_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell false ReferenceProfileData.CoarseLowerShape.Batch0042.a336.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a336 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile336_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link336_checked
    geometry336_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks336_linked.1,←ranks336_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0042.r336.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a336.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0042.ordered336_checked hr ha ho
theorem frozen_frame336 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336 ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds ReferenceProfileData.CoarseLowerShape.Batch0042.a336.bounds
  · rw [←r_profile336_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile336_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry336_linked.2.2.2.2.1
  · exact geometry336_linked.2.2.2.2.2
  · exact r_reference336_checked
  · exact a_reference336_checked
  · exact r_fixed336_linked
  · exact a_fixed336_linked
  · exact time336_checked
  · exact ht
  · exact hw
theorem child_geometry336_checked : ReferenceWeightData.CoarseLowerShape.Batch0084.cert672.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0084.cert672.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0084.cert673.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0084.cert673.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights336 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0084.cert672∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch84_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0084.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0084.cert673∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch84_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0084.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0084.cert672.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0084.cert672.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0084.cert672.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry336_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights672_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0084.cert673.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0084.cert673.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry336_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry336_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights673_linked j (List.mem_finRange j))
theorem actual_frozen_frame336 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame336 (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.flow.timeParameter_mem child_geometry336_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights336 hz)
theorem r_profile337_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r337=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds := by rfl
theorem a_profile337_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a337=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a337.bounds := by rfl
theorem r_fixed337_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 7 := by decide +kernel
theorem a_fixed337_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a337.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.a337.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 9 := by decide +kernel
theorem ranks337_linked : ReferenceRankData.CoarseLowerShape.Batch0042.targetR337=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0042.targetA337=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 1 := by decide +kernel
theorem r_input337_linked : ReferenceRankData.CoarseLowerShape.Batch0042.r337.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds.gauge] := by decide +kernel
theorem a_input337_linked : ReferenceRankData.CoarseLowerShape.Batch0042.a337.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.a337.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.a337.bounds.gauge] := by decide +kernel
theorem geometry337_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.a := by decide +kernel
theorem weights674_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0084.cert674.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights675_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0084.cert675.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time337_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 10)=true := by decide +kernel
theorem r_reference337_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 0)=true := by decide +kernel
theorem a_reference337_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 1)=true := by decide +kernel
theorem rank_r_link337_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r337 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link337_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0042.a337.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a337 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints337 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell true ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r337 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile337_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link337_checked
    geometry337_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell false ReferenceProfileData.CoarseLowerShape.Batch0042.a337.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a337 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile337_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link337_checked
    geometry337_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks337_linked.1,←ranks337_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0042.r337.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a337.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0042.ordered337_checked hr ha ho
theorem frozen_frame337 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337 ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds ReferenceProfileData.CoarseLowerShape.Batch0042.a337.bounds
  · rw [←r_profile337_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile337_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry337_linked.2.2.2.2.1
  · exact geometry337_linked.2.2.2.2.2
  · exact r_reference337_checked
  · exact a_reference337_checked
  · exact r_fixed337_linked
  · exact a_fixed337_linked
  · exact time337_checked
  · exact ht
  · exact hw
theorem child_geometry337_checked : ReferenceWeightData.CoarseLowerShape.Batch0084.cert674.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0084.cert674.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0084.cert675.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0084.cert675.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights337 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0084.cert674∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch84_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0084.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0084.cert675∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch84_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0084.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0084.cert674.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0084.cert674.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0084.cert674.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry337_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights674_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0084.cert675.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0084.cert675.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry337_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry337_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights675_linked j (List.mem_finRange j))
theorem actual_frozen_frame337 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame337 (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.flow.timeParameter_mem child_geometry337_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights337 hz)
theorem r_profile338_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r338=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds := by rfl
theorem a_profile338_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a338=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a338.bounds := by rfl
theorem r_fixed338_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 7 := by decide +kernel
theorem a_fixed338_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a338.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.a338.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 9 := by decide +kernel
theorem ranks338_linked : ReferenceRankData.CoarseLowerShape.Batch0042.targetR338=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0042.targetA338=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 1 := by decide +kernel
theorem r_input338_linked : ReferenceRankData.CoarseLowerShape.Batch0042.r338.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds.gauge] := by decide +kernel
theorem a_input338_linked : ReferenceRankData.CoarseLowerShape.Batch0042.a338.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.a338.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.a338.bounds.gauge] := by decide +kernel
theorem geometry338_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.a := by decide +kernel
theorem weights676_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0084.cert676.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights677_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0084.cert677.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time338_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 10)=true := by decide +kernel
theorem r_reference338_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 0)=true := by decide +kernel
theorem a_reference338_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 1)=true := by decide +kernel
theorem rank_r_link338_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r338 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link338_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0042.a338.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a338 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints338 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell true ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r338 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile338_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link338_checked
    geometry338_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell false ReferenceProfileData.CoarseLowerShape.Batch0042.a338.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a338 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile338_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link338_checked
    geometry338_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks338_linked.1,←ranks338_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0042.r338.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a338.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0042.ordered338_checked hr ha ho
theorem frozen_frame338 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338 ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds ReferenceProfileData.CoarseLowerShape.Batch0042.a338.bounds
  · rw [←r_profile338_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile338_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry338_linked.2.2.2.2.1
  · exact geometry338_linked.2.2.2.2.2
  · exact r_reference338_checked
  · exact a_reference338_checked
  · exact r_fixed338_linked
  · exact a_fixed338_linked
  · exact time338_checked
  · exact ht
  · exact hw
theorem child_geometry338_checked : ReferenceWeightData.CoarseLowerShape.Batch0084.cert676.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0084.cert676.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0084.cert677.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0084.cert677.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights338 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0084.cert676∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch84_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0084.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0084.cert677∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch84_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0084.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0084.cert676.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0084.cert676.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0084.cert676.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry338_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights676_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0084.cert677.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0084.cert677.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry338_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry338_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights677_linked j (List.mem_finRange j))
theorem actual_frozen_frame338 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame338 (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.flow.timeParameter_mem child_geometry338_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights338 hz)
theorem r_profile339_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r339=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds := by rfl
theorem a_profile339_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a339=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a339.bounds := by rfl
theorem r_fixed339_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 7 := by decide +kernel
theorem a_fixed339_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a339.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.a339.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 9 := by decide +kernel
theorem ranks339_linked : ReferenceRankData.CoarseLowerShape.Batch0042.targetR339=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0042.targetA339=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 1 := by decide +kernel
theorem r_input339_linked : ReferenceRankData.CoarseLowerShape.Batch0042.r339.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds.gauge] := by decide +kernel
theorem a_input339_linked : ReferenceRankData.CoarseLowerShape.Batch0042.a339.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.a339.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.a339.bounds.gauge] := by decide +kernel
theorem geometry339_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.a := by decide +kernel
theorem weights678_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0084.cert678.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights679_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0084.cert679.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time339_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 10)=true := by decide +kernel
theorem r_reference339_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 0)=true := by decide +kernel
theorem a_reference339_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 1)=true := by decide +kernel
theorem rank_r_link339_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r339 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link339_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0042.a339.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a339 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints339 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell true ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r339 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile339_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link339_checked
    geometry339_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell false ReferenceProfileData.CoarseLowerShape.Batch0042.a339.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a339 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile339_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link339_checked
    geometry339_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks339_linked.1,←ranks339_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0042.r339.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a339.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0042.ordered339_checked hr ha ho
theorem frozen_frame339 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339 ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds ReferenceProfileData.CoarseLowerShape.Batch0042.a339.bounds
  · rw [←r_profile339_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile339_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry339_linked.2.2.2.2.1
  · exact geometry339_linked.2.2.2.2.2
  · exact r_reference339_checked
  · exact a_reference339_checked
  · exact r_fixed339_linked
  · exact a_fixed339_linked
  · exact time339_checked
  · exact ht
  · exact hw
theorem child_geometry339_checked : ReferenceWeightData.CoarseLowerShape.Batch0084.cert678.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0084.cert678.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0084.cert679.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0084.cert679.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights339 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0084.cert678∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch84_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0084.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0084.cert679∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch84_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0084.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0084.cert678.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0084.cert678.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0084.cert678.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry339_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights678_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0084.cert679.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0084.cert679.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry339_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry339_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights679_linked j (List.mem_finRange j))
theorem actual_frozen_frame339 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame339 (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.flow.timeParameter_mem child_geometry339_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights339 hz)
theorem r_profile340_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r340=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds := by rfl
theorem a_profile340_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a340=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a340.bounds := by rfl
theorem r_fixed340_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 7 := by decide +kernel
theorem a_fixed340_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a340.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.a340.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 9 := by decide +kernel
theorem ranks340_linked : ReferenceRankData.CoarseLowerShape.Batch0042.targetR340=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0042.targetA340=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 1 := by decide +kernel
theorem r_input340_linked : ReferenceRankData.CoarseLowerShape.Batch0042.r340.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds.gauge] := by decide +kernel
theorem a_input340_linked : ReferenceRankData.CoarseLowerShape.Batch0042.a340.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.a340.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.a340.bounds.gauge] := by decide +kernel
theorem geometry340_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.a := by decide +kernel
theorem weights680_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0085.cert680.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights681_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0085.cert681.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time340_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 10)=true := by decide +kernel
theorem r_reference340_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 0)=true := by decide +kernel
theorem a_reference340_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 1)=true := by decide +kernel
theorem rank_r_link340_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r340 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link340_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0042.a340.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a340 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints340 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell true ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r340 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile340_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link340_checked
    geometry340_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell false ReferenceProfileData.CoarseLowerShape.Batch0042.a340.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a340 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile340_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link340_checked
    geometry340_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks340_linked.1,←ranks340_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0042.r340.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a340.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0042.ordered340_checked hr ha ho
theorem frozen_frame340 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340 ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds ReferenceProfileData.CoarseLowerShape.Batch0042.a340.bounds
  · rw [←r_profile340_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile340_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry340_linked.2.2.2.2.1
  · exact geometry340_linked.2.2.2.2.2
  · exact r_reference340_checked
  · exact a_reference340_checked
  · exact r_fixed340_linked
  · exact a_fixed340_linked
  · exact time340_checked
  · exact ht
  · exact hw
theorem child_geometry340_checked : ReferenceWeightData.CoarseLowerShape.Batch0085.cert680.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0085.cert680.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0085.cert681.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0085.cert681.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights340 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0085.cert680∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch85_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0085.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0085.cert681∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch85_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0085.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0085.cert680.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0085.cert680.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0085.cert680.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry340_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights680_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0085.cert681.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0085.cert681.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry340_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry340_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights681_linked j (List.mem_finRange j))
theorem actual_frozen_frame340 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame340 (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.flow.timeParameter_mem child_geometry340_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights340 hz)
theorem r_profile341_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r341=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds := by rfl
theorem a_profile341_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a341=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a341.bounds := by rfl
theorem r_fixed341_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 7 := by decide +kernel
theorem a_fixed341_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a341.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.a341.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 9 := by decide +kernel
theorem ranks341_linked : ReferenceRankData.CoarseLowerShape.Batch0042.targetR341=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0042.targetA341=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 1 := by decide +kernel
theorem r_input341_linked : ReferenceRankData.CoarseLowerShape.Batch0042.r341.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds.gauge] := by decide +kernel
theorem a_input341_linked : ReferenceRankData.CoarseLowerShape.Batch0042.a341.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.a341.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.a341.bounds.gauge] := by decide +kernel
theorem geometry341_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.a := by decide +kernel
theorem weights682_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0085.cert682.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights683_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0085.cert683.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time341_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 10)=true := by decide +kernel
theorem r_reference341_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 0)=true := by decide +kernel
theorem a_reference341_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 1)=true := by decide +kernel
theorem rank_r_link341_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r341 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link341_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0042.a341.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a341 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints341 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell true ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r341 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile341_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link341_checked
    geometry341_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell false ReferenceProfileData.CoarseLowerShape.Batch0042.a341.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a341 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile341_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link341_checked
    geometry341_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks341_linked.1,←ranks341_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0042.r341.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a341.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0042.ordered341_checked hr ha ho
theorem frozen_frame341 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341 ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds ReferenceProfileData.CoarseLowerShape.Batch0042.a341.bounds
  · rw [←r_profile341_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile341_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry341_linked.2.2.2.2.1
  · exact geometry341_linked.2.2.2.2.2
  · exact r_reference341_checked
  · exact a_reference341_checked
  · exact r_fixed341_linked
  · exact a_fixed341_linked
  · exact time341_checked
  · exact ht
  · exact hw
theorem child_geometry341_checked : ReferenceWeightData.CoarseLowerShape.Batch0085.cert682.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0085.cert682.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0085.cert683.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0085.cert683.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights341 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0085.cert682∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch85_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0085.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0085.cert683∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch85_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0085.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0085.cert682.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0085.cert682.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0085.cert682.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry341_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights682_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0085.cert683.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0085.cert683.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry341_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry341_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights683_linked j (List.mem_finRange j))
theorem actual_frozen_frame341 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame341 (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.flow.timeParameter_mem child_geometry341_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights341 hz)
theorem r_profile342_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r342=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds := by rfl
theorem a_profile342_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a342=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a342.bounds := by rfl
theorem r_fixed342_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 7 := by decide +kernel
theorem a_fixed342_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a342.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.a342.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 9 := by decide +kernel
theorem ranks342_linked : ReferenceRankData.CoarseLowerShape.Batch0042.targetR342=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0042.targetA342=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 1 := by decide +kernel
theorem r_input342_linked : ReferenceRankData.CoarseLowerShape.Batch0042.r342.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds.gauge] := by decide +kernel
theorem a_input342_linked : ReferenceRankData.CoarseLowerShape.Batch0042.a342.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.a342.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.a342.bounds.gauge] := by decide +kernel
theorem geometry342_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.a := by decide +kernel
theorem weights684_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0085.cert684.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights685_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0085.cert685.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time342_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 10)=true := by decide +kernel
theorem r_reference342_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 0)=true := by decide +kernel
theorem a_reference342_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 1)=true := by decide +kernel
theorem rank_r_link342_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r342 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link342_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0042.a342.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a342 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints342 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell true ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r342 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile342_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link342_checked
    geometry342_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell false ReferenceProfileData.CoarseLowerShape.Batch0042.a342.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a342 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile342_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link342_checked
    geometry342_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks342_linked.1,←ranks342_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0042.r342.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a342.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0042.ordered342_checked hr ha ho
theorem frozen_frame342 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342 ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds ReferenceProfileData.CoarseLowerShape.Batch0042.a342.bounds
  · rw [←r_profile342_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile342_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry342_linked.2.2.2.2.1
  · exact geometry342_linked.2.2.2.2.2
  · exact r_reference342_checked
  · exact a_reference342_checked
  · exact r_fixed342_linked
  · exact a_fixed342_linked
  · exact time342_checked
  · exact ht
  · exact hw
theorem child_geometry342_checked : ReferenceWeightData.CoarseLowerShape.Batch0085.cert684.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0085.cert684.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0085.cert685.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0085.cert685.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights342 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0085.cert684∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch85_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0085.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0085.cert685∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch85_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0085.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0085.cert684.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0085.cert684.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0085.cert684.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry342_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights684_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0085.cert685.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0085.cert685.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry342_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry342_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights685_linked j (List.mem_finRange j))
theorem actual_frozen_frame342 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame342 (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.flow.timeParameter_mem child_geometry342_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights342 hz)
theorem r_profile343_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r343=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds := by rfl
theorem a_profile343_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a343=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a343.bounds := by rfl
theorem r_fixed343_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 7 := by decide +kernel
theorem a_fixed343_linked : ReferenceProfileData.CoarseLowerShape.Batch0042.a343.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0042.a343.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 9 := by decide +kernel
theorem ranks343_linked : ReferenceRankData.CoarseLowerShape.Batch0042.targetR343=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0042.targetA343=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 1 := by decide +kernel
theorem r_input343_linked : ReferenceRankData.CoarseLowerShape.Batch0042.r343.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds.gauge] := by decide +kernel
theorem a_input343_linked : ReferenceRankData.CoarseLowerShape.Batch0042.a343.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0042.a343.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0042.a343.bounds.gauge] := by decide +kernel
theorem geometry343_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.a := by decide +kernel
theorem weights686_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0085.cert686.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights687_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0085.cert687.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time343_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 10)=true := by decide +kernel
theorem r_reference343_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 0)=true := by decide +kernel
theorem a_reference343_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 1)=true := by decide +kernel
theorem rank_r_link343_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r343 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link343_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0042.a343.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a343 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints343 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell true ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds ReferenceRankData.CoarseLowerShape.Batch0042.r343 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile343_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link343_checked
    geometry343_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell false ReferenceProfileData.CoarseLowerShape.Batch0042.a343.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a343 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile343_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0042.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0042.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link343_checked
    geometry343_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks343_linked.1,←ranks343_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0042.r343.bounds ReferenceRankData.CoarseLowerShape.Batch0042.a343.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0042.ordered343_checked hr ha ho
theorem frozen_frame343 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343 ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds ReferenceProfileData.CoarseLowerShape.Batch0042.a343.bounds
  · rw [←r_profile343_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile343_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry343_linked.2.2.2.2.1
  · exact geometry343_linked.2.2.2.2.2
  · exact r_reference343_checked
  · exact a_reference343_checked
  · exact r_fixed343_linked
  · exact a_fixed343_linked
  · exact time343_checked
  · exact ht
  · exact hw
theorem child_geometry343_checked : ReferenceWeightData.CoarseLowerShape.Batch0085.cert686.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0085.cert686.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0085.cert687.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0085.cert687.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights343 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0085.cert686∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch85_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0085.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0085.cert687∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch85_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0085.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0085.cert686.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0085.cert686.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0085.cert686.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry343_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights686_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0085.cert687.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0085.cert687.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry343_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry343_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights687_linked j (List.mem_finRange j))
theorem actual_frozen_frame343 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame343 (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.flow.timeParameter_mem child_geometry343_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights343 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell336),(ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell337),(ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell338),(ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell339),(ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell340),(ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell341),(ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell342),(ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0042.cell343)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0042.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0042.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame336 hz
  · exact fun z hz=>actual_frozen_frame337 hz
  · exact fun z hz=>actual_frozen_frame338 hz
  · exact fun z hz=>actual_frozen_frame339 hz
  · exact fun z hz=>actual_frozen_frame340 hz
  · exact fun z hz=>actual_frozen_frame341 hz
  · exact fun z hz=>actual_frozen_frame342 hz
  · exact fun z hz=>actual_frozen_frame343 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints336 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints337 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints338 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints339 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints340 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints341 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints342 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints343 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry336_linked.1,geometry336_linked.2.1,geometry336_linked.2.2.1,geometry336_linked.2.2.2.1⟩
  · exact ⟨geometry337_linked.1,geometry337_linked.2.1,geometry337_linked.2.2.1,geometry337_linked.2.2.2.1⟩
  · exact ⟨geometry338_linked.1,geometry338_linked.2.1,geometry338_linked.2.2.1,geometry338_linked.2.2.2.1⟩
  · exact ⟨geometry339_linked.1,geometry339_linked.2.1,geometry339_linked.2.2.1,geometry339_linked.2.2.2.1⟩
  · exact ⟨geometry340_linked.1,geometry340_linked.2.1,geometry340_linked.2.2.1,geometry340_linked.2.2.2.1⟩
  · exact ⟨geometry341_linked.1,geometry341_linked.2.1,geometry341_linked.2.2.1,geometry341_linked.2.2.2.1⟩
  · exact ⟨geometry342_linked.1,geometry342_linked.2.1,geometry342_linked.2.2.1,geometry342_linked.2.2.2.1⟩
  · exact ⟨geometry343_linked.1,geometry343_linked.2.1,geometry343_linked.2.2.1,geometry343_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.a336.bounds,?_,geometry336_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a336.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile336_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds,?_,geometry336_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert336.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r336.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile336_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.a337.bounds,?_,geometry337_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a337.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile337_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds,?_,geometry337_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert337.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r337.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile337_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.a338.bounds,?_,geometry338_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a338.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile338_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds,?_,geometry338_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert338.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r338.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile338_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.a339.bounds,?_,geometry339_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a339.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile339_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds,?_,geometry339_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert339.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r339.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile339_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.a340.bounds,?_,geometry340_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a340.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile340_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds,?_,geometry340_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert340.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r340.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile340_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.a341.bounds,?_,geometry341_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a341.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile341_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds,?_,geometry341_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert341.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r341.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile341_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.a342.bounds,?_,geometry342_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a342.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile342_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds,?_,geometry342_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert342.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r342.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile342_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.a343.bounds,?_,geometry343_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0042.a343.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile343_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds,?_,geometry343_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0042.cert343.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0042.r343.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile343_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0042.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0042.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0042

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0043
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch86_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0086.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0086.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile344_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.r344=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds := by rfl
theorem a_profile344_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.a344=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0043.a344.bounds := by rfl
theorem r_fixed344_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 7 := by decide +kernel
theorem a_fixed344_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.a344.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.a344.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 9 := by decide +kernel
theorem ranks344_linked : ReferenceRankData.CoarseLowerShape.Batch0043.targetR344=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0043.targetA344=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 1 := by decide +kernel
theorem r_input344_linked : ReferenceRankData.CoarseLowerShape.Batch0043.r344.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds.gauge] := by decide +kernel
theorem a_input344_linked : ReferenceRankData.CoarseLowerShape.Batch0043.a344.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0043.a344.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0043.a344.bounds.gauge] := by decide +kernel
theorem geometry344_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.a := by decide +kernel
theorem weights688_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0086.cert688.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights689_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0086.cert689.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time344_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 10)=true := by decide +kernel
theorem r_reference344_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 0)=true := by decide +kernel
theorem a_reference344_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 1)=true := by decide +kernel
theorem rank_r_link344_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds ReferenceRankData.CoarseLowerShape.Batch0043.r344 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link344_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0043.a344.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a344 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints344 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell true ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds ReferenceRankData.CoarseLowerShape.Batch0043.r344 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile344_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0043.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0043.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link344_checked
    geometry344_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell false ReferenceProfileData.CoarseLowerShape.Batch0043.a344.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a344 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile344_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0043.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0043.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link344_checked
    geometry344_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks344_linked.1,←ranks344_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0043.r344.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a344.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0043.ordered344_checked hr ha ho
theorem frozen_frame344 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344 ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds ReferenceProfileData.CoarseLowerShape.Batch0043.a344.bounds
  · rw [←r_profile344_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile344_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry344_linked.2.2.2.2.1
  · exact geometry344_linked.2.2.2.2.2
  · exact r_reference344_checked
  · exact a_reference344_checked
  · exact r_fixed344_linked
  · exact a_fixed344_linked
  · exact time344_checked
  · exact ht
  · exact hw
theorem child_geometry344_checked : ReferenceWeightData.CoarseLowerShape.Batch0086.cert688.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0086.cert688.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0086.cert689.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0086.cert689.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights344 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0086.cert688∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch86_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0086.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0086.cert689∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch86_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0086.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0086.cert688.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0086.cert688.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0086.cert688.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry344_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights688_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0086.cert689.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0086.cert689.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry344_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry344_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights689_linked j (List.mem_finRange j))
theorem actual_frozen_frame344 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame344 (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.flow.timeParameter_mem child_geometry344_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights344 hz)
theorem r_profile345_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.r345=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds := by rfl
theorem a_profile345_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.a345=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0043.a345.bounds := by rfl
theorem r_fixed345_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 7 := by decide +kernel
theorem a_fixed345_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.a345.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.a345.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 9 := by decide +kernel
theorem ranks345_linked : ReferenceRankData.CoarseLowerShape.Batch0043.targetR345=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0043.targetA345=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 1 := by decide +kernel
theorem r_input345_linked : ReferenceRankData.CoarseLowerShape.Batch0043.r345.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds.gauge] := by decide +kernel
theorem a_input345_linked : ReferenceRankData.CoarseLowerShape.Batch0043.a345.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0043.a345.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0043.a345.bounds.gauge] := by decide +kernel
theorem geometry345_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.a := by decide +kernel
theorem weights690_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0086.cert690.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights691_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0086.cert691.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time345_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 10)=true := by decide +kernel
theorem r_reference345_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 0)=true := by decide +kernel
theorem a_reference345_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 1)=true := by decide +kernel
theorem rank_r_link345_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds ReferenceRankData.CoarseLowerShape.Batch0043.r345 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link345_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0043.a345.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a345 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints345 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell true ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds ReferenceRankData.CoarseLowerShape.Batch0043.r345 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile345_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0043.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0043.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link345_checked
    geometry345_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell false ReferenceProfileData.CoarseLowerShape.Batch0043.a345.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a345 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile345_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0043.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0043.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link345_checked
    geometry345_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks345_linked.1,←ranks345_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0043.r345.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a345.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0043.ordered345_checked hr ha ho
theorem frozen_frame345 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345 ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds ReferenceProfileData.CoarseLowerShape.Batch0043.a345.bounds
  · rw [←r_profile345_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile345_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry345_linked.2.2.2.2.1
  · exact geometry345_linked.2.2.2.2.2
  · exact r_reference345_checked
  · exact a_reference345_checked
  · exact r_fixed345_linked
  · exact a_fixed345_linked
  · exact time345_checked
  · exact ht
  · exact hw
theorem child_geometry345_checked : ReferenceWeightData.CoarseLowerShape.Batch0086.cert690.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0086.cert690.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0086.cert691.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0086.cert691.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights345 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0086.cert690∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch86_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0086.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0086.cert691∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch86_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0086.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0086.cert690.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0086.cert690.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0086.cert690.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry345_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights690_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0086.cert691.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0086.cert691.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry345_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry345_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights691_linked j (List.mem_finRange j))
theorem actual_frozen_frame345 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame345 (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.flow.timeParameter_mem child_geometry345_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights345 hz)
theorem r_profile346_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.r346=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds := by rfl
theorem a_profile346_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.a346=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0043.a346.bounds := by rfl
theorem r_fixed346_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 7 := by decide +kernel
theorem a_fixed346_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.a346.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.a346.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 9 := by decide +kernel
theorem ranks346_linked : ReferenceRankData.CoarseLowerShape.Batch0043.targetR346=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0043.targetA346=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 1 := by decide +kernel
theorem r_input346_linked : ReferenceRankData.CoarseLowerShape.Batch0043.r346.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds.gauge] := by decide +kernel
theorem a_input346_linked : ReferenceRankData.CoarseLowerShape.Batch0043.a346.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0043.a346.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0043.a346.bounds.gauge] := by decide +kernel
theorem geometry346_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.a := by decide +kernel
theorem weights692_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0086.cert692.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights693_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0086.cert693.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time346_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 10)=true := by decide +kernel
theorem r_reference346_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 0)=true := by decide +kernel
theorem a_reference346_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 1)=true := by decide +kernel
theorem rank_r_link346_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds ReferenceRankData.CoarseLowerShape.Batch0043.r346 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link346_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0043.a346.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a346 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints346 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell true ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds ReferenceRankData.CoarseLowerShape.Batch0043.r346 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile346_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0043.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0043.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link346_checked
    geometry346_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell false ReferenceProfileData.CoarseLowerShape.Batch0043.a346.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a346 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile346_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0043.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0043.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link346_checked
    geometry346_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks346_linked.1,←ranks346_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0043.r346.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a346.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0043.ordered346_checked hr ha ho
theorem frozen_frame346 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346 ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds ReferenceProfileData.CoarseLowerShape.Batch0043.a346.bounds
  · rw [←r_profile346_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile346_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry346_linked.2.2.2.2.1
  · exact geometry346_linked.2.2.2.2.2
  · exact r_reference346_checked
  · exact a_reference346_checked
  · exact r_fixed346_linked
  · exact a_fixed346_linked
  · exact time346_checked
  · exact ht
  · exact hw
theorem child_geometry346_checked : ReferenceWeightData.CoarseLowerShape.Batch0086.cert692.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0086.cert692.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0086.cert693.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0086.cert693.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights346 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0086.cert692∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch86_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0086.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0086.cert693∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch86_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0086.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0086.cert692.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0086.cert692.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0086.cert692.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry346_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights692_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0086.cert693.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0086.cert693.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry346_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry346_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights693_linked j (List.mem_finRange j))
theorem actual_frozen_frame346 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame346 (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.flow.timeParameter_mem child_geometry346_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights346 hz)
theorem r_profile347_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.r347=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds := by rfl
theorem a_profile347_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.a347=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0043.a347.bounds := by rfl
theorem r_fixed347_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 7 := by decide +kernel
theorem a_fixed347_linked : ReferenceProfileData.CoarseLowerShape.Batch0043.a347.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0043.a347.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 9 := by decide +kernel
theorem ranks347_linked : ReferenceRankData.CoarseLowerShape.Batch0043.targetR347=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0043.targetA347=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 1 := by decide +kernel
theorem r_input347_linked : ReferenceRankData.CoarseLowerShape.Batch0043.r347.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds.gauge] := by decide +kernel
theorem a_input347_linked : ReferenceRankData.CoarseLowerShape.Batch0043.a347.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0043.a347.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0043.a347.bounds.gauge] := by decide +kernel
theorem geometry347_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.a := by decide +kernel
theorem weights694_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0086.cert694.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights695_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0086.cert695.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time347_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 10)=true := by decide +kernel
theorem r_reference347_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 0)=true := by decide +kernel
theorem a_reference347_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 1)=true := by decide +kernel
theorem rank_r_link347_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds ReferenceRankData.CoarseLowerShape.Batch0043.r347 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link347_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0043.a347.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a347 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints347 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell true ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds ReferenceRankData.CoarseLowerShape.Batch0043.r347 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile347_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0043.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0043.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link347_checked
    geometry347_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell false ReferenceProfileData.CoarseLowerShape.Batch0043.a347.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a347 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile347_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0043.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0043.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link347_checked
    geometry347_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks347_linked.1,←ranks347_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0043.r347.bounds ReferenceRankData.CoarseLowerShape.Batch0043.a347.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0043.ordered347_checked hr ha ho
theorem frozen_frame347 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347 ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds ReferenceProfileData.CoarseLowerShape.Batch0043.a347.bounds
  · rw [←r_profile347_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile347_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry347_linked.2.2.2.2.1
  · exact geometry347_linked.2.2.2.2.2
  · exact r_reference347_checked
  · exact a_reference347_checked
  · exact r_fixed347_linked
  · exact a_fixed347_linked
  · exact time347_checked
  · exact ht
  · exact hw
theorem child_geometry347_checked : ReferenceWeightData.CoarseLowerShape.Batch0086.cert694.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0086.cert694.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0086.cert695.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0086.cert695.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights347 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0086.cert694∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch86_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0086.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0086.cert695∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch86_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0086.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0086.cert694.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0086.cert694.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0086.cert694.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry347_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights694_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0086.cert695.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0086.cert695.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry347_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry347_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights695_linked j (List.mem_finRange j))
theorem actual_frozen_frame347 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame347 (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.flow.timeParameter_mem child_geometry347_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights347 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell344),(ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell345),(ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell346),(ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0043.cell347)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0043.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0043.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame344 hz
  · exact fun z hz=>actual_frozen_frame345 hz
  · exact fun z hz=>actual_frozen_frame346 hz
  · exact fun z hz=>actual_frozen_frame347 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints344 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints345 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints346 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints347 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨geometry344_linked.1,geometry344_linked.2.1,geometry344_linked.2.2.1,geometry344_linked.2.2.2.1⟩
  · exact ⟨geometry345_linked.1,geometry345_linked.2.1,geometry345_linked.2.2.1,geometry345_linked.2.2.2.1⟩
  · exact ⟨geometry346_linked.1,geometry346_linked.2.1,geometry346_linked.2.2.1,geometry346_linked.2.2.2.1⟩
  · exact ⟨geometry347_linked.1,geometry347_linked.2.1,geometry347_linked.2.2.1,geometry347_linked.2.2.2.1⟩
theorem rank_lower_checked : sources.all (fun p=>decide ((1/4:ℚ)≤p.1.flow.segment.left.r))=true := by decide +kernel
theorem branches_checked : sources.all (fun p=>p.1.branchGeometryCheck TransportReferenceData.CoarseLowerShape.data.leftContact)=true := by decide +kernel
theorem rank_crop_checked : sources.all (fun p=>p.1.flow.rankCropCheck TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact true && p.1.flow.rankCropCheck TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact false)=true := by decide +kernel
theorem source_rank_frames : ∀ p∈sources,∀ useR : Bool,∃ bounds : ReferenceProfileBox,
    (p.1.rankProfile useR bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true ∧
    (p.1.rankProfile useR bounds).lo≤(p.1.rankProfile useR bounds).hi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0043.a344.bounds,?_,geometry344_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0043.a344.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile344_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds,?_,geometry344_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert344.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0043.r344.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile344_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0043.a345.bounds,?_,geometry345_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0043.a345.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile345_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds,?_,geometry345_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert345.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0043.r345.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile345_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0043.a346.bounds,?_,geometry346_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0043.a346.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile346_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds,?_,geometry346_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert346.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0043.r346.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile346_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0043.a347.bounds,?_,geometry347_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0043.a347.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile347_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds,?_,geometry347_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0043.cert347.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0043.r347.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile347_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0043.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0043.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0043
