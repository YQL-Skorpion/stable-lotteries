import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0033_0036
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0033_0036
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0073_0076
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0034_0037
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0035_0038
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Bundle0032_0035
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0037_0040
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0037_0040
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0077_0080
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0038_0041
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0039_0042

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0036
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch72_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0072.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0072.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch73_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0073.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0073.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile288_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r288=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds := by rfl
theorem a_profile288_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a288=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a288.bounds := by rfl
theorem r_fixed288_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 7 := by decide +kernel
theorem a_fixed288_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a288.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.a288.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 9 := by decide +kernel
theorem ranks288_linked : ReferenceRankData.CoarseLowerShape.Batch0036.targetR288=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0036.targetA288=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 1 := by decide +kernel
theorem r_input288_linked : ReferenceRankData.CoarseLowerShape.Batch0036.r288.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds.gauge] := by decide +kernel
theorem a_input288_linked : ReferenceRankData.CoarseLowerShape.Batch0036.a288.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.a288.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.a288.bounds.gauge] := by decide +kernel
theorem geometry288_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.a := by decide +kernel
theorem weights576_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0072.cert576.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights577_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0072.cert577.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time288_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 10)=true := by decide +kernel
theorem r_reference288_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 0)=true := by decide +kernel
theorem a_reference288_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 1)=true := by decide +kernel
theorem rank_r_link288_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r288 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link288_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0036.a288.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a288 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints288 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell true ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r288 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile288_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link288_checked
    geometry288_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell false ReferenceProfileData.CoarseLowerShape.Batch0036.a288.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a288 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile288_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link288_checked
    geometry288_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks288_linked.1,←ranks288_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0036.r288.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a288.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0036.ordered288_checked hr ha ho
theorem frozen_frame288 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288 ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds ReferenceProfileData.CoarseLowerShape.Batch0036.a288.bounds
  · rw [←r_profile288_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile288_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry288_linked.2.2.2.2.1
  · exact geometry288_linked.2.2.2.2.2
  · exact r_reference288_checked
  · exact a_reference288_checked
  · exact r_fixed288_linked
  · exact a_fixed288_linked
  · exact time288_checked
  · exact ht
  · exact hw
theorem child_geometry288_checked : ReferenceWeightData.CoarseLowerShape.Batch0072.cert576.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0072.cert576.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0072.cert577.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0072.cert577.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights288 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0072.cert576∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch72_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0072.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0072.cert577∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch72_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0072.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0072.cert576.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0072.cert576.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0072.cert576.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry288_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights576_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0072.cert577.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0072.cert577.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry288_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry288_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights577_linked j (List.mem_finRange j))
theorem actual_frozen_frame288 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame288 (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.flow.timeParameter_mem child_geometry288_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights288 hz)
theorem r_profile289_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r289=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds := by rfl
theorem a_profile289_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a289=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a289.bounds := by rfl
theorem r_fixed289_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 7 := by decide +kernel
theorem a_fixed289_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a289.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.a289.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 9 := by decide +kernel
theorem ranks289_linked : ReferenceRankData.CoarseLowerShape.Batch0036.targetR289=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0036.targetA289=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 1 := by decide +kernel
theorem r_input289_linked : ReferenceRankData.CoarseLowerShape.Batch0036.r289.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds.gauge] := by decide +kernel
theorem a_input289_linked : ReferenceRankData.CoarseLowerShape.Batch0036.a289.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.a289.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.a289.bounds.gauge] := by decide +kernel
theorem geometry289_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.a := by decide +kernel
theorem weights578_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0072.cert578.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights579_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0072.cert579.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time289_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 10)=true := by decide +kernel
theorem r_reference289_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 0)=true := by decide +kernel
theorem a_reference289_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 1)=true := by decide +kernel
theorem rank_r_link289_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r289 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link289_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0036.a289.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a289 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints289 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell true ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r289 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile289_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link289_checked
    geometry289_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell false ReferenceProfileData.CoarseLowerShape.Batch0036.a289.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a289 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile289_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link289_checked
    geometry289_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks289_linked.1,←ranks289_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0036.r289.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a289.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0036.ordered289_checked hr ha ho
theorem frozen_frame289 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289 ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds ReferenceProfileData.CoarseLowerShape.Batch0036.a289.bounds
  · rw [←r_profile289_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile289_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry289_linked.2.2.2.2.1
  · exact geometry289_linked.2.2.2.2.2
  · exact r_reference289_checked
  · exact a_reference289_checked
  · exact r_fixed289_linked
  · exact a_fixed289_linked
  · exact time289_checked
  · exact ht
  · exact hw
theorem child_geometry289_checked : ReferenceWeightData.CoarseLowerShape.Batch0072.cert578.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0072.cert578.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0072.cert579.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0072.cert579.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights289 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0072.cert578∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch72_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0072.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0072.cert579∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch72_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0072.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0072.cert578.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0072.cert578.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0072.cert578.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry289_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights578_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0072.cert579.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0072.cert579.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry289_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry289_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights579_linked j (List.mem_finRange j))
theorem actual_frozen_frame289 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame289 (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.flow.timeParameter_mem child_geometry289_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights289 hz)
theorem r_profile290_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r290=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds := by rfl
theorem a_profile290_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a290=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a290.bounds := by rfl
theorem r_fixed290_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 7 := by decide +kernel
theorem a_fixed290_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a290.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.a290.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 9 := by decide +kernel
theorem ranks290_linked : ReferenceRankData.CoarseLowerShape.Batch0036.targetR290=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0036.targetA290=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 1 := by decide +kernel
theorem r_input290_linked : ReferenceRankData.CoarseLowerShape.Batch0036.r290.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds.gauge] := by decide +kernel
theorem a_input290_linked : ReferenceRankData.CoarseLowerShape.Batch0036.a290.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.a290.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.a290.bounds.gauge] := by decide +kernel
theorem geometry290_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.a := by decide +kernel
theorem weights580_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0072.cert580.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights581_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0072.cert581.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time290_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 10)=true := by decide +kernel
theorem r_reference290_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 0)=true := by decide +kernel
theorem a_reference290_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 1)=true := by decide +kernel
theorem rank_r_link290_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r290 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link290_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0036.a290.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a290 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints290 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell true ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r290 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile290_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link290_checked
    geometry290_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell false ReferenceProfileData.CoarseLowerShape.Batch0036.a290.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a290 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile290_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link290_checked
    geometry290_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks290_linked.1,←ranks290_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0036.r290.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a290.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0036.ordered290_checked hr ha ho
theorem frozen_frame290 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290 ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds ReferenceProfileData.CoarseLowerShape.Batch0036.a290.bounds
  · rw [←r_profile290_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile290_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry290_linked.2.2.2.2.1
  · exact geometry290_linked.2.2.2.2.2
  · exact r_reference290_checked
  · exact a_reference290_checked
  · exact r_fixed290_linked
  · exact a_fixed290_linked
  · exact time290_checked
  · exact ht
  · exact hw
theorem child_geometry290_checked : ReferenceWeightData.CoarseLowerShape.Batch0072.cert580.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0072.cert580.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0072.cert581.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0072.cert581.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights290 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0072.cert580∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch72_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0072.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0072.cert581∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch72_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0072.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0072.cert580.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0072.cert580.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0072.cert580.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry290_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights580_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0072.cert581.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0072.cert581.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry290_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry290_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights581_linked j (List.mem_finRange j))
theorem actual_frozen_frame290 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame290 (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.flow.timeParameter_mem child_geometry290_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights290 hz)
theorem r_profile291_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r291=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds := by rfl
theorem a_profile291_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a291=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a291.bounds := by rfl
theorem r_fixed291_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 7 := by decide +kernel
theorem a_fixed291_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a291.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.a291.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 9 := by decide +kernel
theorem ranks291_linked : ReferenceRankData.CoarseLowerShape.Batch0036.targetR291=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0036.targetA291=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 1 := by decide +kernel
theorem r_input291_linked : ReferenceRankData.CoarseLowerShape.Batch0036.r291.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds.gauge] := by decide +kernel
theorem a_input291_linked : ReferenceRankData.CoarseLowerShape.Batch0036.a291.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.a291.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.a291.bounds.gauge] := by decide +kernel
theorem geometry291_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.a := by decide +kernel
theorem weights582_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0072.cert582.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights583_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0072.cert583.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time291_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 10)=true := by decide +kernel
theorem r_reference291_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 0)=true := by decide +kernel
theorem a_reference291_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 1)=true := by decide +kernel
theorem rank_r_link291_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r291 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link291_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0036.a291.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a291 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints291 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell true ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r291 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile291_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link291_checked
    geometry291_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell false ReferenceProfileData.CoarseLowerShape.Batch0036.a291.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a291 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile291_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link291_checked
    geometry291_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks291_linked.1,←ranks291_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0036.r291.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a291.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0036.ordered291_checked hr ha ho
theorem frozen_frame291 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291 ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds ReferenceProfileData.CoarseLowerShape.Batch0036.a291.bounds
  · rw [←r_profile291_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile291_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry291_linked.2.2.2.2.1
  · exact geometry291_linked.2.2.2.2.2
  · exact r_reference291_checked
  · exact a_reference291_checked
  · exact r_fixed291_linked
  · exact a_fixed291_linked
  · exact time291_checked
  · exact ht
  · exact hw
theorem child_geometry291_checked : ReferenceWeightData.CoarseLowerShape.Batch0072.cert582.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0072.cert582.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0072.cert583.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0072.cert583.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights291 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0072.cert582∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch72_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0072.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0072.cert583∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch72_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0072.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0072.cert582.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0072.cert582.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0072.cert582.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry291_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights582_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0072.cert583.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0072.cert583.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry291_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry291_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights583_linked j (List.mem_finRange j))
theorem actual_frozen_frame291 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame291 (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.flow.timeParameter_mem child_geometry291_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights291 hz)
theorem r_profile292_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r292=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds := by rfl
theorem a_profile292_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a292=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a292.bounds := by rfl
theorem r_fixed292_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 7 := by decide +kernel
theorem a_fixed292_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a292.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.a292.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 9 := by decide +kernel
theorem ranks292_linked : ReferenceRankData.CoarseLowerShape.Batch0036.targetR292=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0036.targetA292=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 1 := by decide +kernel
theorem r_input292_linked : ReferenceRankData.CoarseLowerShape.Batch0036.r292.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds.gauge] := by decide +kernel
theorem a_input292_linked : ReferenceRankData.CoarseLowerShape.Batch0036.a292.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.a292.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.a292.bounds.gauge] := by decide +kernel
theorem geometry292_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.a := by decide +kernel
theorem weights584_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0073.cert584.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights585_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0073.cert585.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time292_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 10)=true := by decide +kernel
theorem r_reference292_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 0)=true := by decide +kernel
theorem a_reference292_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 1)=true := by decide +kernel
theorem rank_r_link292_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r292 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link292_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0036.a292.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a292 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints292 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell true ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r292 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile292_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link292_checked
    geometry292_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell false ReferenceProfileData.CoarseLowerShape.Batch0036.a292.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a292 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile292_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link292_checked
    geometry292_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks292_linked.1,←ranks292_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0036.r292.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a292.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0036.ordered292_checked hr ha ho
theorem frozen_frame292 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292 ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds ReferenceProfileData.CoarseLowerShape.Batch0036.a292.bounds
  · rw [←r_profile292_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile292_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry292_linked.2.2.2.2.1
  · exact geometry292_linked.2.2.2.2.2
  · exact r_reference292_checked
  · exact a_reference292_checked
  · exact r_fixed292_linked
  · exact a_fixed292_linked
  · exact time292_checked
  · exact ht
  · exact hw
theorem child_geometry292_checked : ReferenceWeightData.CoarseLowerShape.Batch0073.cert584.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0073.cert584.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0073.cert585.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0073.cert585.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights292 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0073.cert584∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch73_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0073.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0073.cert585∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch73_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0073.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0073.cert584.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0073.cert584.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0073.cert584.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry292_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights584_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0073.cert585.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0073.cert585.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry292_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry292_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights585_linked j (List.mem_finRange j))
theorem actual_frozen_frame292 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame292 (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.flow.timeParameter_mem child_geometry292_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights292 hz)
theorem r_profile293_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r293=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds := by rfl
theorem a_profile293_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a293=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a293.bounds := by rfl
theorem r_fixed293_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 7 := by decide +kernel
theorem a_fixed293_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a293.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.a293.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 9 := by decide +kernel
theorem ranks293_linked : ReferenceRankData.CoarseLowerShape.Batch0036.targetR293=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0036.targetA293=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 1 := by decide +kernel
theorem r_input293_linked : ReferenceRankData.CoarseLowerShape.Batch0036.r293.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds.gauge] := by decide +kernel
theorem a_input293_linked : ReferenceRankData.CoarseLowerShape.Batch0036.a293.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.a293.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.a293.bounds.gauge] := by decide +kernel
theorem geometry293_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.a := by decide +kernel
theorem weights586_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0073.cert586.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights587_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0073.cert587.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time293_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 10)=true := by decide +kernel
theorem r_reference293_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 0)=true := by decide +kernel
theorem a_reference293_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 1)=true := by decide +kernel
theorem rank_r_link293_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r293 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link293_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0036.a293.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a293 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints293 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell true ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r293 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile293_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link293_checked
    geometry293_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell false ReferenceProfileData.CoarseLowerShape.Batch0036.a293.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a293 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile293_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link293_checked
    geometry293_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks293_linked.1,←ranks293_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0036.r293.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a293.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0036.ordered293_checked hr ha ho
theorem frozen_frame293 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293 ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds ReferenceProfileData.CoarseLowerShape.Batch0036.a293.bounds
  · rw [←r_profile293_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile293_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry293_linked.2.2.2.2.1
  · exact geometry293_linked.2.2.2.2.2
  · exact r_reference293_checked
  · exact a_reference293_checked
  · exact r_fixed293_linked
  · exact a_fixed293_linked
  · exact time293_checked
  · exact ht
  · exact hw
theorem child_geometry293_checked : ReferenceWeightData.CoarseLowerShape.Batch0073.cert586.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0073.cert586.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0073.cert587.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0073.cert587.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights293 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0073.cert586∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch73_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0073.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0073.cert587∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch73_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0073.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0073.cert586.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0073.cert586.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0073.cert586.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry293_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights586_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0073.cert587.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0073.cert587.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry293_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry293_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights587_linked j (List.mem_finRange j))
theorem actual_frozen_frame293 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame293 (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.flow.timeParameter_mem child_geometry293_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights293 hz)
theorem r_profile294_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r294=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds := by rfl
theorem a_profile294_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a294=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a294.bounds := by rfl
theorem r_fixed294_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 7 := by decide +kernel
theorem a_fixed294_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a294.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.a294.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 9 := by decide +kernel
theorem ranks294_linked : ReferenceRankData.CoarseLowerShape.Batch0036.targetR294=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0036.targetA294=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 1 := by decide +kernel
theorem r_input294_linked : ReferenceRankData.CoarseLowerShape.Batch0036.r294.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds.gauge] := by decide +kernel
theorem a_input294_linked : ReferenceRankData.CoarseLowerShape.Batch0036.a294.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.a294.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.a294.bounds.gauge] := by decide +kernel
theorem geometry294_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.a := by decide +kernel
theorem weights588_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0073.cert588.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights589_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0073.cert589.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time294_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 10)=true := by decide +kernel
theorem r_reference294_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 0)=true := by decide +kernel
theorem a_reference294_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 1)=true := by decide +kernel
theorem rank_r_link294_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r294 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link294_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0036.a294.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a294 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints294 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell true ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r294 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile294_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link294_checked
    geometry294_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell false ReferenceProfileData.CoarseLowerShape.Batch0036.a294.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a294 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile294_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link294_checked
    geometry294_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks294_linked.1,←ranks294_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0036.r294.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a294.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0036.ordered294_checked hr ha ho
theorem frozen_frame294 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294 ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds ReferenceProfileData.CoarseLowerShape.Batch0036.a294.bounds
  · rw [←r_profile294_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile294_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry294_linked.2.2.2.2.1
  · exact geometry294_linked.2.2.2.2.2
  · exact r_reference294_checked
  · exact a_reference294_checked
  · exact r_fixed294_linked
  · exact a_fixed294_linked
  · exact time294_checked
  · exact ht
  · exact hw
theorem child_geometry294_checked : ReferenceWeightData.CoarseLowerShape.Batch0073.cert588.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0073.cert588.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0073.cert589.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0073.cert589.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights294 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0073.cert588∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch73_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0073.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0073.cert589∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch73_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0073.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0073.cert588.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0073.cert588.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0073.cert588.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry294_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights588_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0073.cert589.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0073.cert589.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry294_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry294_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights589_linked j (List.mem_finRange j))
theorem actual_frozen_frame294 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame294 (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.flow.timeParameter_mem child_geometry294_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights294 hz)
theorem r_profile295_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r295=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds := by rfl
theorem a_profile295_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a295=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a295.bounds := by rfl
theorem r_fixed295_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 7 := by decide +kernel
theorem a_fixed295_linked : ReferenceProfileData.CoarseLowerShape.Batch0036.a295.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0036.a295.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 9 := by decide +kernel
theorem ranks295_linked : ReferenceRankData.CoarseLowerShape.Batch0036.targetR295=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0036.targetA295=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 1 := by decide +kernel
theorem r_input295_linked : ReferenceRankData.CoarseLowerShape.Batch0036.r295.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds.gauge] := by decide +kernel
theorem a_input295_linked : ReferenceRankData.CoarseLowerShape.Batch0036.a295.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0036.a295.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0036.a295.bounds.gauge] := by decide +kernel
theorem geometry295_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.a := by decide +kernel
theorem weights590_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0073.cert590.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights591_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0073.cert591.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time295_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 10)=true := by decide +kernel
theorem r_reference295_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 0)=true := by decide +kernel
theorem a_reference295_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 1)=true := by decide +kernel
theorem rank_r_link295_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r295 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link295_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0036.a295.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a295 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints295 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell true ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds ReferenceRankData.CoarseLowerShape.Batch0036.r295 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile295_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link295_checked
    geometry295_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell false ReferenceProfileData.CoarseLowerShape.Batch0036.a295.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a295 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile295_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0036.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0036.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link295_checked
    geometry295_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks295_linked.1,←ranks295_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0036.r295.bounds ReferenceRankData.CoarseLowerShape.Batch0036.a295.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0036.ordered295_checked hr ha ho
theorem frozen_frame295 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295 ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds ReferenceProfileData.CoarseLowerShape.Batch0036.a295.bounds
  · rw [←r_profile295_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile295_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry295_linked.2.2.2.2.1
  · exact geometry295_linked.2.2.2.2.2
  · exact r_reference295_checked
  · exact a_reference295_checked
  · exact r_fixed295_linked
  · exact a_fixed295_linked
  · exact time295_checked
  · exact ht
  · exact hw
theorem child_geometry295_checked : ReferenceWeightData.CoarseLowerShape.Batch0073.cert590.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0073.cert590.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0073.cert591.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0073.cert591.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights295 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0073.cert590∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch73_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0073.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0073.cert591∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch73_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0073.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0073.cert590.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0073.cert590.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0073.cert590.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry295_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights590_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0073.cert591.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0073.cert591.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry295_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry295_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights591_linked j (List.mem_finRange j))
theorem actual_frozen_frame295 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame295 (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.flow.timeParameter_mem child_geometry295_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights295 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell288),(ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell289),(ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell290),(ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell291),(ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell292),(ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell293),(ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell294),(ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0036.cell295)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0036.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0036.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame288 hz
  · exact fun z hz=>actual_frozen_frame289 hz
  · exact fun z hz=>actual_frozen_frame290 hz
  · exact fun z hz=>actual_frozen_frame291 hz
  · exact fun z hz=>actual_frozen_frame292 hz
  · exact fun z hz=>actual_frozen_frame293 hz
  · exact fun z hz=>actual_frozen_frame294 hz
  · exact fun z hz=>actual_frozen_frame295 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints288 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints289 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints290 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints291 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints292 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints293 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints294 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints295 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry288_linked.1,geometry288_linked.2.1,geometry288_linked.2.2.1,geometry288_linked.2.2.2.1⟩
  · exact ⟨geometry289_linked.1,geometry289_linked.2.1,geometry289_linked.2.2.1,geometry289_linked.2.2.2.1⟩
  · exact ⟨geometry290_linked.1,geometry290_linked.2.1,geometry290_linked.2.2.1,geometry290_linked.2.2.2.1⟩
  · exact ⟨geometry291_linked.1,geometry291_linked.2.1,geometry291_linked.2.2.1,geometry291_linked.2.2.2.1⟩
  · exact ⟨geometry292_linked.1,geometry292_linked.2.1,geometry292_linked.2.2.1,geometry292_linked.2.2.2.1⟩
  · exact ⟨geometry293_linked.1,geometry293_linked.2.1,geometry293_linked.2.2.1,geometry293_linked.2.2.2.1⟩
  · exact ⟨geometry294_linked.1,geometry294_linked.2.1,geometry294_linked.2.2.1,geometry294_linked.2.2.2.1⟩
  · exact ⟨geometry295_linked.1,geometry295_linked.2.1,geometry295_linked.2.2.1,geometry295_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.a288.bounds,?_,geometry288_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a288.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile288_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds,?_,geometry288_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert288.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r288.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile288_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.a289.bounds,?_,geometry289_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a289.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile289_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds,?_,geometry289_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert289.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r289.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile289_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.a290.bounds,?_,geometry290_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a290.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile290_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds,?_,geometry290_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert290.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r290.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile290_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.a291.bounds,?_,geometry291_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a291.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile291_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds,?_,geometry291_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert291.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r291.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile291_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.a292.bounds,?_,geometry292_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a292.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile292_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds,?_,geometry292_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert292.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r292.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile292_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.a293.bounds,?_,geometry293_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a293.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile293_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds,?_,geometry293_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert293.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r293.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile293_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.a294.bounds,?_,geometry294_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a294.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile294_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds,?_,geometry294_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert294.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r294.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile294_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.a295.bounds,?_,geometry295_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0036.a295.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile295_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds,?_,geometry295_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0036.cert295.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0036.r295.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile295_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0036.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0036.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0036

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0037
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch74_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0074.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0074.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch75_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0075.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0075.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile296_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r296=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds := by rfl
theorem a_profile296_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a296=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a296.bounds := by rfl
theorem r_fixed296_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 7 := by decide +kernel
theorem a_fixed296_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a296.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.a296.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 9 := by decide +kernel
theorem ranks296_linked : ReferenceRankData.CoarseLowerShape.Batch0037.targetR296=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0037.targetA296=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 1 := by decide +kernel
theorem r_input296_linked : ReferenceRankData.CoarseLowerShape.Batch0037.r296.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds.gauge] := by decide +kernel
theorem a_input296_linked : ReferenceRankData.CoarseLowerShape.Batch0037.a296.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.a296.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.a296.bounds.gauge] := by decide +kernel
theorem geometry296_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.a := by decide +kernel
theorem weights592_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0074.cert592.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights593_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0074.cert593.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time296_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 10)=true := by decide +kernel
theorem r_reference296_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 0)=true := by decide +kernel
theorem a_reference296_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 1)=true := by decide +kernel
theorem rank_r_link296_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r296 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link296_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0037.a296.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a296 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints296 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell true ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r296 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile296_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link296_checked
    geometry296_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell false ReferenceProfileData.CoarseLowerShape.Batch0037.a296.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a296 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile296_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link296_checked
    geometry296_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks296_linked.1,←ranks296_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0037.r296.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a296.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0037.ordered296_checked hr ha ho
theorem frozen_frame296 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296 ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds ReferenceProfileData.CoarseLowerShape.Batch0037.a296.bounds
  · rw [←r_profile296_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile296_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry296_linked.2.2.2.2.1
  · exact geometry296_linked.2.2.2.2.2
  · exact r_reference296_checked
  · exact a_reference296_checked
  · exact r_fixed296_linked
  · exact a_fixed296_linked
  · exact time296_checked
  · exact ht
  · exact hw
theorem child_geometry296_checked : ReferenceWeightData.CoarseLowerShape.Batch0074.cert592.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0074.cert592.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0074.cert593.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0074.cert593.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights296 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0074.cert592∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch74_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0074.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0074.cert593∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch74_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0074.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0074.cert592.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0074.cert592.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0074.cert592.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry296_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights592_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0074.cert593.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0074.cert593.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry296_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry296_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights593_linked j (List.mem_finRange j))
theorem actual_frozen_frame296 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame296 (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.flow.timeParameter_mem child_geometry296_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights296 hz)
theorem r_profile297_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r297=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds := by rfl
theorem a_profile297_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a297=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a297.bounds := by rfl
theorem r_fixed297_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 7 := by decide +kernel
theorem a_fixed297_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a297.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.a297.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 9 := by decide +kernel
theorem ranks297_linked : ReferenceRankData.CoarseLowerShape.Batch0037.targetR297=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0037.targetA297=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 1 := by decide +kernel
theorem r_input297_linked : ReferenceRankData.CoarseLowerShape.Batch0037.r297.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds.gauge] := by decide +kernel
theorem a_input297_linked : ReferenceRankData.CoarseLowerShape.Batch0037.a297.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.a297.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.a297.bounds.gauge] := by decide +kernel
theorem geometry297_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.a := by decide +kernel
theorem weights594_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0074.cert594.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights595_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0074.cert595.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time297_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 10)=true := by decide +kernel
theorem r_reference297_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 0)=true := by decide +kernel
theorem a_reference297_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 1)=true := by decide +kernel
theorem rank_r_link297_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r297 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link297_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0037.a297.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a297 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints297 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell true ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r297 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile297_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link297_checked
    geometry297_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell false ReferenceProfileData.CoarseLowerShape.Batch0037.a297.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a297 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile297_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link297_checked
    geometry297_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks297_linked.1,←ranks297_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0037.r297.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a297.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0037.ordered297_checked hr ha ho
theorem frozen_frame297 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297 ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds ReferenceProfileData.CoarseLowerShape.Batch0037.a297.bounds
  · rw [←r_profile297_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile297_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry297_linked.2.2.2.2.1
  · exact geometry297_linked.2.2.2.2.2
  · exact r_reference297_checked
  · exact a_reference297_checked
  · exact r_fixed297_linked
  · exact a_fixed297_linked
  · exact time297_checked
  · exact ht
  · exact hw
theorem child_geometry297_checked : ReferenceWeightData.CoarseLowerShape.Batch0074.cert594.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0074.cert594.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0074.cert595.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0074.cert595.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights297 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0074.cert594∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch74_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0074.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0074.cert595∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch74_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0074.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0074.cert594.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0074.cert594.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0074.cert594.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry297_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights594_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0074.cert595.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0074.cert595.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry297_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry297_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights595_linked j (List.mem_finRange j))
theorem actual_frozen_frame297 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame297 (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.flow.timeParameter_mem child_geometry297_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights297 hz)
theorem r_profile298_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r298=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds := by rfl
theorem a_profile298_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a298=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a298.bounds := by rfl
theorem r_fixed298_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 7 := by decide +kernel
theorem a_fixed298_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a298.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.a298.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 9 := by decide +kernel
theorem ranks298_linked : ReferenceRankData.CoarseLowerShape.Batch0037.targetR298=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0037.targetA298=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 1 := by decide +kernel
theorem r_input298_linked : ReferenceRankData.CoarseLowerShape.Batch0037.r298.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds.gauge] := by decide +kernel
theorem a_input298_linked : ReferenceRankData.CoarseLowerShape.Batch0037.a298.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.a298.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.a298.bounds.gauge] := by decide +kernel
theorem geometry298_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.a := by decide +kernel
theorem weights596_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0074.cert596.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights597_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0074.cert597.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time298_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 10)=true := by decide +kernel
theorem r_reference298_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 0)=true := by decide +kernel
theorem a_reference298_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 1)=true := by decide +kernel
theorem rank_r_link298_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r298 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link298_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0037.a298.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a298 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints298 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell true ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r298 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile298_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link298_checked
    geometry298_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell false ReferenceProfileData.CoarseLowerShape.Batch0037.a298.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a298 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile298_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link298_checked
    geometry298_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks298_linked.1,←ranks298_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0037.r298.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a298.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0037.ordered298_checked hr ha ho
theorem frozen_frame298 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298 ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds ReferenceProfileData.CoarseLowerShape.Batch0037.a298.bounds
  · rw [←r_profile298_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile298_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry298_linked.2.2.2.2.1
  · exact geometry298_linked.2.2.2.2.2
  · exact r_reference298_checked
  · exact a_reference298_checked
  · exact r_fixed298_linked
  · exact a_fixed298_linked
  · exact time298_checked
  · exact ht
  · exact hw
theorem child_geometry298_checked : ReferenceWeightData.CoarseLowerShape.Batch0074.cert596.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0074.cert596.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0074.cert597.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0074.cert597.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights298 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0074.cert596∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch74_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0074.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0074.cert597∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch74_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0074.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0074.cert596.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0074.cert596.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0074.cert596.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry298_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights596_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0074.cert597.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0074.cert597.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry298_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry298_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights597_linked j (List.mem_finRange j))
theorem actual_frozen_frame298 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame298 (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.flow.timeParameter_mem child_geometry298_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights298 hz)
theorem r_profile299_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r299=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds := by rfl
theorem a_profile299_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a299=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a299.bounds := by rfl
theorem r_fixed299_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 7 := by decide +kernel
theorem a_fixed299_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a299.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.a299.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 9 := by decide +kernel
theorem ranks299_linked : ReferenceRankData.CoarseLowerShape.Batch0037.targetR299=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0037.targetA299=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 1 := by decide +kernel
theorem r_input299_linked : ReferenceRankData.CoarseLowerShape.Batch0037.r299.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds.gauge] := by decide +kernel
theorem a_input299_linked : ReferenceRankData.CoarseLowerShape.Batch0037.a299.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.a299.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.a299.bounds.gauge] := by decide +kernel
theorem geometry299_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.a := by decide +kernel
theorem weights598_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0074.cert598.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights599_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0074.cert599.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time299_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 10)=true := by decide +kernel
theorem r_reference299_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 0)=true := by decide +kernel
theorem a_reference299_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 1)=true := by decide +kernel
theorem rank_r_link299_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r299 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link299_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0037.a299.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a299 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints299 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell true ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r299 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile299_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link299_checked
    geometry299_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell false ReferenceProfileData.CoarseLowerShape.Batch0037.a299.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a299 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile299_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link299_checked
    geometry299_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks299_linked.1,←ranks299_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0037.r299.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a299.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0037.ordered299_checked hr ha ho
theorem frozen_frame299 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299 ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds ReferenceProfileData.CoarseLowerShape.Batch0037.a299.bounds
  · rw [←r_profile299_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile299_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry299_linked.2.2.2.2.1
  · exact geometry299_linked.2.2.2.2.2
  · exact r_reference299_checked
  · exact a_reference299_checked
  · exact r_fixed299_linked
  · exact a_fixed299_linked
  · exact time299_checked
  · exact ht
  · exact hw
theorem child_geometry299_checked : ReferenceWeightData.CoarseLowerShape.Batch0074.cert598.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0074.cert598.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0074.cert599.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0074.cert599.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights299 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0074.cert598∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch74_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0074.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0074.cert599∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch74_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0074.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0074.cert598.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0074.cert598.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0074.cert598.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry299_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights598_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0074.cert599.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0074.cert599.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry299_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry299_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights599_linked j (List.mem_finRange j))
theorem actual_frozen_frame299 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame299 (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.flow.timeParameter_mem child_geometry299_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights299 hz)
theorem r_profile300_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r300=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds := by rfl
theorem a_profile300_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a300=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a300.bounds := by rfl
theorem r_fixed300_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 7 := by decide +kernel
theorem a_fixed300_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a300.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.a300.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 9 := by decide +kernel
theorem ranks300_linked : ReferenceRankData.CoarseLowerShape.Batch0037.targetR300=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0037.targetA300=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 1 := by decide +kernel
theorem r_input300_linked : ReferenceRankData.CoarseLowerShape.Batch0037.r300.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds.gauge] := by decide +kernel
theorem a_input300_linked : ReferenceRankData.CoarseLowerShape.Batch0037.a300.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.a300.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.a300.bounds.gauge] := by decide +kernel
theorem geometry300_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.a := by decide +kernel
theorem weights600_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0075.cert600.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights601_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0075.cert601.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time300_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 10)=true := by decide +kernel
theorem r_reference300_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 0)=true := by decide +kernel
theorem a_reference300_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 1)=true := by decide +kernel
theorem rank_r_link300_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r300 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link300_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0037.a300.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a300 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints300 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell true ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r300 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile300_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link300_checked
    geometry300_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell false ReferenceProfileData.CoarseLowerShape.Batch0037.a300.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a300 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile300_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link300_checked
    geometry300_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks300_linked.1,←ranks300_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0037.r300.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a300.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0037.ordered300_checked hr ha ho
theorem frozen_frame300 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300 ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds ReferenceProfileData.CoarseLowerShape.Batch0037.a300.bounds
  · rw [←r_profile300_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile300_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry300_linked.2.2.2.2.1
  · exact geometry300_linked.2.2.2.2.2
  · exact r_reference300_checked
  · exact a_reference300_checked
  · exact r_fixed300_linked
  · exact a_fixed300_linked
  · exact time300_checked
  · exact ht
  · exact hw
theorem child_geometry300_checked : ReferenceWeightData.CoarseLowerShape.Batch0075.cert600.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0075.cert600.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0075.cert601.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0075.cert601.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights300 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0075.cert600∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch75_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0075.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0075.cert601∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch75_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0075.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0075.cert600.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0075.cert600.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0075.cert600.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry300_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights600_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0075.cert601.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0075.cert601.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry300_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry300_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights601_linked j (List.mem_finRange j))
theorem actual_frozen_frame300 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame300 (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.flow.timeParameter_mem child_geometry300_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights300 hz)
theorem r_profile301_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r301=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds := by rfl
theorem a_profile301_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a301=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a301.bounds := by rfl
theorem r_fixed301_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 7 := by decide +kernel
theorem a_fixed301_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a301.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.a301.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 9 := by decide +kernel
theorem ranks301_linked : ReferenceRankData.CoarseLowerShape.Batch0037.targetR301=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0037.targetA301=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 1 := by decide +kernel
theorem r_input301_linked : ReferenceRankData.CoarseLowerShape.Batch0037.r301.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds.gauge] := by decide +kernel
theorem a_input301_linked : ReferenceRankData.CoarseLowerShape.Batch0037.a301.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.a301.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.a301.bounds.gauge] := by decide +kernel
theorem geometry301_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.a := by decide +kernel
theorem weights602_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0075.cert602.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights603_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0075.cert603.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time301_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 10)=true := by decide +kernel
theorem r_reference301_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 0)=true := by decide +kernel
theorem a_reference301_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 1)=true := by decide +kernel
theorem rank_r_link301_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r301 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link301_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0037.a301.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a301 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints301 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell true ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r301 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile301_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link301_checked
    geometry301_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell false ReferenceProfileData.CoarseLowerShape.Batch0037.a301.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a301 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile301_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link301_checked
    geometry301_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks301_linked.1,←ranks301_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0037.r301.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a301.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0037.ordered301_checked hr ha ho
theorem frozen_frame301 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301 ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds ReferenceProfileData.CoarseLowerShape.Batch0037.a301.bounds
  · rw [←r_profile301_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile301_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry301_linked.2.2.2.2.1
  · exact geometry301_linked.2.2.2.2.2
  · exact r_reference301_checked
  · exact a_reference301_checked
  · exact r_fixed301_linked
  · exact a_fixed301_linked
  · exact time301_checked
  · exact ht
  · exact hw
theorem child_geometry301_checked : ReferenceWeightData.CoarseLowerShape.Batch0075.cert602.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0075.cert602.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0075.cert603.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0075.cert603.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights301 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0075.cert602∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch75_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0075.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0075.cert603∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch75_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0075.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0075.cert602.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0075.cert602.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0075.cert602.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry301_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights602_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0075.cert603.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0075.cert603.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry301_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry301_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights603_linked j (List.mem_finRange j))
theorem actual_frozen_frame301 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame301 (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.flow.timeParameter_mem child_geometry301_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights301 hz)
theorem r_profile302_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r302=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds := by rfl
theorem a_profile302_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a302=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a302.bounds := by rfl
theorem r_fixed302_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 7 := by decide +kernel
theorem a_fixed302_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a302.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.a302.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 9 := by decide +kernel
theorem ranks302_linked : ReferenceRankData.CoarseLowerShape.Batch0037.targetR302=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0037.targetA302=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 1 := by decide +kernel
theorem r_input302_linked : ReferenceRankData.CoarseLowerShape.Batch0037.r302.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds.gauge] := by decide +kernel
theorem a_input302_linked : ReferenceRankData.CoarseLowerShape.Batch0037.a302.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.a302.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.a302.bounds.gauge] := by decide +kernel
theorem geometry302_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.a := by decide +kernel
theorem weights604_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0075.cert604.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights605_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0075.cert605.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time302_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 10)=true := by decide +kernel
theorem r_reference302_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 0)=true := by decide +kernel
theorem a_reference302_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 1)=true := by decide +kernel
theorem rank_r_link302_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r302 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link302_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0037.a302.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a302 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints302 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell true ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r302 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile302_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link302_checked
    geometry302_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell false ReferenceProfileData.CoarseLowerShape.Batch0037.a302.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a302 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile302_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link302_checked
    geometry302_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks302_linked.1,←ranks302_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0037.r302.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a302.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0037.ordered302_checked hr ha ho
theorem frozen_frame302 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302 ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds ReferenceProfileData.CoarseLowerShape.Batch0037.a302.bounds
  · rw [←r_profile302_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile302_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry302_linked.2.2.2.2.1
  · exact geometry302_linked.2.2.2.2.2
  · exact r_reference302_checked
  · exact a_reference302_checked
  · exact r_fixed302_linked
  · exact a_fixed302_linked
  · exact time302_checked
  · exact ht
  · exact hw
theorem child_geometry302_checked : ReferenceWeightData.CoarseLowerShape.Batch0075.cert604.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0075.cert604.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0075.cert605.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0075.cert605.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights302 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0075.cert604∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch75_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0075.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0075.cert605∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch75_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0075.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0075.cert604.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0075.cert604.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0075.cert604.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry302_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights604_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0075.cert605.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0075.cert605.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry302_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry302_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights605_linked j (List.mem_finRange j))
theorem actual_frozen_frame302 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame302 (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.flow.timeParameter_mem child_geometry302_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights302 hz)
theorem r_profile303_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r303=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds := by rfl
theorem a_profile303_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a303=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a303.bounds := by rfl
theorem r_fixed303_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 7 := by decide +kernel
theorem a_fixed303_linked : ReferenceProfileData.CoarseLowerShape.Batch0037.a303.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0037.a303.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 9 := by decide +kernel
theorem ranks303_linked : ReferenceRankData.CoarseLowerShape.Batch0037.targetR303=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0037.targetA303=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 1 := by decide +kernel
theorem r_input303_linked : ReferenceRankData.CoarseLowerShape.Batch0037.r303.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds.gauge] := by decide +kernel
theorem a_input303_linked : ReferenceRankData.CoarseLowerShape.Batch0037.a303.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0037.a303.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0037.a303.bounds.gauge] := by decide +kernel
theorem geometry303_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.a := by decide +kernel
theorem weights606_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0075.cert606.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights607_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0075.cert607.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time303_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 10)=true := by decide +kernel
theorem r_reference303_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 0)=true := by decide +kernel
theorem a_reference303_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 1)=true := by decide +kernel
theorem rank_r_link303_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r303 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link303_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0037.a303.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a303 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints303 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell true ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds ReferenceRankData.CoarseLowerShape.Batch0037.r303 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile303_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link303_checked
    geometry303_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell false ReferenceProfileData.CoarseLowerShape.Batch0037.a303.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a303 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile303_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0037.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0037.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link303_checked
    geometry303_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks303_linked.1,←ranks303_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0037.r303.bounds ReferenceRankData.CoarseLowerShape.Batch0037.a303.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0037.ordered303_checked hr ha ho
theorem frozen_frame303 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303 ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds ReferenceProfileData.CoarseLowerShape.Batch0037.a303.bounds
  · rw [←r_profile303_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile303_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry303_linked.2.2.2.2.1
  · exact geometry303_linked.2.2.2.2.2
  · exact r_reference303_checked
  · exact a_reference303_checked
  · exact r_fixed303_linked
  · exact a_fixed303_linked
  · exact time303_checked
  · exact ht
  · exact hw
theorem child_geometry303_checked : ReferenceWeightData.CoarseLowerShape.Batch0075.cert606.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0075.cert606.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0075.cert607.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0075.cert607.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights303 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0075.cert606∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch75_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0075.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0075.cert607∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch75_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0075.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0075.cert606.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0075.cert606.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0075.cert606.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry303_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights606_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0075.cert607.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0075.cert607.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry303_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry303_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights607_linked j (List.mem_finRange j))
theorem actual_frozen_frame303 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame303 (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.flow.timeParameter_mem child_geometry303_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights303 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell296),(ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell297),(ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell298),(ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell299),(ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell300),(ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell301),(ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell302),(ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0037.cell303)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0037.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0037.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame296 hz
  · exact fun z hz=>actual_frozen_frame297 hz
  · exact fun z hz=>actual_frozen_frame298 hz
  · exact fun z hz=>actual_frozen_frame299 hz
  · exact fun z hz=>actual_frozen_frame300 hz
  · exact fun z hz=>actual_frozen_frame301 hz
  · exact fun z hz=>actual_frozen_frame302 hz
  · exact fun z hz=>actual_frozen_frame303 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints296 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints297 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints298 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints299 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints300 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints301 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints302 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints303 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry296_linked.1,geometry296_linked.2.1,geometry296_linked.2.2.1,geometry296_linked.2.2.2.1⟩
  · exact ⟨geometry297_linked.1,geometry297_linked.2.1,geometry297_linked.2.2.1,geometry297_linked.2.2.2.1⟩
  · exact ⟨geometry298_linked.1,geometry298_linked.2.1,geometry298_linked.2.2.1,geometry298_linked.2.2.2.1⟩
  · exact ⟨geometry299_linked.1,geometry299_linked.2.1,geometry299_linked.2.2.1,geometry299_linked.2.2.2.1⟩
  · exact ⟨geometry300_linked.1,geometry300_linked.2.1,geometry300_linked.2.2.1,geometry300_linked.2.2.2.1⟩
  · exact ⟨geometry301_linked.1,geometry301_linked.2.1,geometry301_linked.2.2.1,geometry301_linked.2.2.2.1⟩
  · exact ⟨geometry302_linked.1,geometry302_linked.2.1,geometry302_linked.2.2.1,geometry302_linked.2.2.2.1⟩
  · exact ⟨geometry303_linked.1,geometry303_linked.2.1,geometry303_linked.2.2.1,geometry303_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.a296.bounds,?_,geometry296_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a296.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile296_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds,?_,geometry296_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert296.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r296.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile296_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.a297.bounds,?_,geometry297_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a297.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile297_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds,?_,geometry297_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert297.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r297.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile297_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.a298.bounds,?_,geometry298_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a298.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile298_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds,?_,geometry298_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert298.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r298.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile298_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.a299.bounds,?_,geometry299_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a299.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile299_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds,?_,geometry299_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert299.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r299.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile299_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.a300.bounds,?_,geometry300_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a300.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile300_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds,?_,geometry300_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert300.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r300.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile300_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.a301.bounds,?_,geometry301_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a301.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile301_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds,?_,geometry301_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert301.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r301.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile301_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.a302.bounds,?_,geometry302_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a302.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile302_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds,?_,geometry302_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert302.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r302.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile302_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.a303.bounds,?_,geometry303_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0037.a303.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile303_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds,?_,geometry303_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0037.cert303.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0037.r303.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile303_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0037.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0037.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0037

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0038
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch76_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0076.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0076.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch77_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0077.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0077.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile304_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r304=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds := by rfl
theorem a_profile304_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a304=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a304.bounds := by rfl
theorem r_fixed304_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 7 := by decide +kernel
theorem a_fixed304_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a304.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.a304.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 9 := by decide +kernel
theorem ranks304_linked : ReferenceRankData.CoarseLowerShape.Batch0038.targetR304=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0038.targetA304=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 1 := by decide +kernel
theorem r_input304_linked : ReferenceRankData.CoarseLowerShape.Batch0038.r304.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds.gauge] := by decide +kernel
theorem a_input304_linked : ReferenceRankData.CoarseLowerShape.Batch0038.a304.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.a304.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.a304.bounds.gauge] := by decide +kernel
theorem geometry304_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.a := by decide +kernel
theorem weights608_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0076.cert608.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights609_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0076.cert609.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time304_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 10)=true := by decide +kernel
theorem r_reference304_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 0)=true := by decide +kernel
theorem a_reference304_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 1)=true := by decide +kernel
theorem rank_r_link304_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r304 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link304_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0038.a304.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a304 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints304 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell true ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r304 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile304_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link304_checked
    geometry304_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell false ReferenceProfileData.CoarseLowerShape.Batch0038.a304.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a304 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile304_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link304_checked
    geometry304_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks304_linked.1,←ranks304_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0038.r304.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a304.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0038.ordered304_checked hr ha ho
theorem frozen_frame304 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304 ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds ReferenceProfileData.CoarseLowerShape.Batch0038.a304.bounds
  · rw [←r_profile304_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile304_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry304_linked.2.2.2.2.1
  · exact geometry304_linked.2.2.2.2.2
  · exact r_reference304_checked
  · exact a_reference304_checked
  · exact r_fixed304_linked
  · exact a_fixed304_linked
  · exact time304_checked
  · exact ht
  · exact hw
theorem child_geometry304_checked : ReferenceWeightData.CoarseLowerShape.Batch0076.cert608.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0076.cert608.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0076.cert609.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0076.cert609.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights304 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0076.cert608∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch76_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0076.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0076.cert609∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch76_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0076.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0076.cert608.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0076.cert608.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0076.cert608.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry304_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights608_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0076.cert609.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0076.cert609.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry304_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry304_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights609_linked j (List.mem_finRange j))
theorem actual_frozen_frame304 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame304 (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.flow.timeParameter_mem child_geometry304_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights304 hz)
theorem r_profile305_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r305=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds := by rfl
theorem a_profile305_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a305=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a305.bounds := by rfl
theorem r_fixed305_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 7 := by decide +kernel
theorem a_fixed305_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a305.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.a305.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 9 := by decide +kernel
theorem ranks305_linked : ReferenceRankData.CoarseLowerShape.Batch0038.targetR305=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0038.targetA305=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 1 := by decide +kernel
theorem r_input305_linked : ReferenceRankData.CoarseLowerShape.Batch0038.r305.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds.gauge] := by decide +kernel
theorem a_input305_linked : ReferenceRankData.CoarseLowerShape.Batch0038.a305.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.a305.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.a305.bounds.gauge] := by decide +kernel
theorem geometry305_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.a := by decide +kernel
theorem weights610_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0076.cert610.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights611_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0076.cert611.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time305_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 10)=true := by decide +kernel
theorem r_reference305_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 0)=true := by decide +kernel
theorem a_reference305_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 1)=true := by decide +kernel
theorem rank_r_link305_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r305 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link305_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0038.a305.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a305 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints305 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell true ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r305 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile305_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link305_checked
    geometry305_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell false ReferenceProfileData.CoarseLowerShape.Batch0038.a305.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a305 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile305_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link305_checked
    geometry305_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks305_linked.1,←ranks305_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0038.r305.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a305.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0038.ordered305_checked hr ha ho
theorem frozen_frame305 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305 ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds ReferenceProfileData.CoarseLowerShape.Batch0038.a305.bounds
  · rw [←r_profile305_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile305_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry305_linked.2.2.2.2.1
  · exact geometry305_linked.2.2.2.2.2
  · exact r_reference305_checked
  · exact a_reference305_checked
  · exact r_fixed305_linked
  · exact a_fixed305_linked
  · exact time305_checked
  · exact ht
  · exact hw
theorem child_geometry305_checked : ReferenceWeightData.CoarseLowerShape.Batch0076.cert610.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0076.cert610.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0076.cert611.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0076.cert611.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights305 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0076.cert610∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch76_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0076.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0076.cert611∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch76_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0076.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0076.cert610.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0076.cert610.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0076.cert610.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry305_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights610_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0076.cert611.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0076.cert611.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry305_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry305_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights611_linked j (List.mem_finRange j))
theorem actual_frozen_frame305 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame305 (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.flow.timeParameter_mem child_geometry305_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights305 hz)
theorem r_profile306_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r306=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds := by rfl
theorem a_profile306_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a306=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a306.bounds := by rfl
theorem r_fixed306_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 7 := by decide +kernel
theorem a_fixed306_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a306.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.a306.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 9 := by decide +kernel
theorem ranks306_linked : ReferenceRankData.CoarseLowerShape.Batch0038.targetR306=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0038.targetA306=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 1 := by decide +kernel
theorem r_input306_linked : ReferenceRankData.CoarseLowerShape.Batch0038.r306.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds.gauge] := by decide +kernel
theorem a_input306_linked : ReferenceRankData.CoarseLowerShape.Batch0038.a306.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.a306.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.a306.bounds.gauge] := by decide +kernel
theorem geometry306_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.a := by decide +kernel
theorem weights612_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0076.cert612.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights613_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0076.cert613.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time306_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 10)=true := by decide +kernel
theorem r_reference306_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 0)=true := by decide +kernel
theorem a_reference306_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 1)=true := by decide +kernel
theorem rank_r_link306_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r306 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link306_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0038.a306.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a306 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints306 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell true ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r306 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile306_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link306_checked
    geometry306_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell false ReferenceProfileData.CoarseLowerShape.Batch0038.a306.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a306 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile306_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link306_checked
    geometry306_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks306_linked.1,←ranks306_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0038.r306.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a306.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0038.ordered306_checked hr ha ho
theorem frozen_frame306 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306 ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds ReferenceProfileData.CoarseLowerShape.Batch0038.a306.bounds
  · rw [←r_profile306_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile306_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry306_linked.2.2.2.2.1
  · exact geometry306_linked.2.2.2.2.2
  · exact r_reference306_checked
  · exact a_reference306_checked
  · exact r_fixed306_linked
  · exact a_fixed306_linked
  · exact time306_checked
  · exact ht
  · exact hw
theorem child_geometry306_checked : ReferenceWeightData.CoarseLowerShape.Batch0076.cert612.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0076.cert612.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0076.cert613.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0076.cert613.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights306 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0076.cert612∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch76_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0076.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0076.cert613∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch76_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0076.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0076.cert612.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0076.cert612.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0076.cert612.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry306_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights612_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0076.cert613.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0076.cert613.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry306_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry306_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights613_linked j (List.mem_finRange j))
theorem actual_frozen_frame306 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame306 (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.flow.timeParameter_mem child_geometry306_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights306 hz)
theorem r_profile307_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r307=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds := by rfl
theorem a_profile307_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a307=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a307.bounds := by rfl
theorem r_fixed307_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 7 := by decide +kernel
theorem a_fixed307_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a307.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.a307.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 9 := by decide +kernel
theorem ranks307_linked : ReferenceRankData.CoarseLowerShape.Batch0038.targetR307=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0038.targetA307=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 1 := by decide +kernel
theorem r_input307_linked : ReferenceRankData.CoarseLowerShape.Batch0038.r307.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds.gauge] := by decide +kernel
theorem a_input307_linked : ReferenceRankData.CoarseLowerShape.Batch0038.a307.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.a307.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.a307.bounds.gauge] := by decide +kernel
theorem geometry307_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.a := by decide +kernel
theorem weights614_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0076.cert614.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights615_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0076.cert615.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time307_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 10)=true := by decide +kernel
theorem r_reference307_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 0)=true := by decide +kernel
theorem a_reference307_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 1)=true := by decide +kernel
theorem rank_r_link307_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r307 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link307_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0038.a307.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a307 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints307 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell true ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r307 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile307_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link307_checked
    geometry307_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell false ReferenceProfileData.CoarseLowerShape.Batch0038.a307.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a307 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile307_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link307_checked
    geometry307_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks307_linked.1,←ranks307_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0038.r307.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a307.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0038.ordered307_checked hr ha ho
theorem frozen_frame307 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307 ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds ReferenceProfileData.CoarseLowerShape.Batch0038.a307.bounds
  · rw [←r_profile307_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile307_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry307_linked.2.2.2.2.1
  · exact geometry307_linked.2.2.2.2.2
  · exact r_reference307_checked
  · exact a_reference307_checked
  · exact r_fixed307_linked
  · exact a_fixed307_linked
  · exact time307_checked
  · exact ht
  · exact hw
theorem child_geometry307_checked : ReferenceWeightData.CoarseLowerShape.Batch0076.cert614.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0076.cert614.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0076.cert615.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0076.cert615.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights307 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0076.cert614∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch76_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0076.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0076.cert615∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch76_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0076.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0076.cert614.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0076.cert614.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0076.cert614.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry307_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights614_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0076.cert615.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0076.cert615.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry307_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry307_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights615_linked j (List.mem_finRange j))
theorem actual_frozen_frame307 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame307 (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.flow.timeParameter_mem child_geometry307_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights307 hz)
theorem r_profile308_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r308=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds := by rfl
theorem a_profile308_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a308=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a308.bounds := by rfl
theorem r_fixed308_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 7 := by decide +kernel
theorem a_fixed308_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a308.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.a308.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 9 := by decide +kernel
theorem ranks308_linked : ReferenceRankData.CoarseLowerShape.Batch0038.targetR308=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0038.targetA308=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 1 := by decide +kernel
theorem r_input308_linked : ReferenceRankData.CoarseLowerShape.Batch0038.r308.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds.gauge] := by decide +kernel
theorem a_input308_linked : ReferenceRankData.CoarseLowerShape.Batch0038.a308.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.a308.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.a308.bounds.gauge] := by decide +kernel
theorem geometry308_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.a := by decide +kernel
theorem weights616_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0077.cert616.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights617_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0077.cert617.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time308_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 10)=true := by decide +kernel
theorem r_reference308_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 0)=true := by decide +kernel
theorem a_reference308_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 1)=true := by decide +kernel
theorem rank_r_link308_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r308 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link308_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0038.a308.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a308 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints308 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell true ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r308 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile308_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link308_checked
    geometry308_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell false ReferenceProfileData.CoarseLowerShape.Batch0038.a308.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a308 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile308_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link308_checked
    geometry308_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks308_linked.1,←ranks308_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0038.r308.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a308.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0038.ordered308_checked hr ha ho
theorem frozen_frame308 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308 ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds ReferenceProfileData.CoarseLowerShape.Batch0038.a308.bounds
  · rw [←r_profile308_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile308_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry308_linked.2.2.2.2.1
  · exact geometry308_linked.2.2.2.2.2
  · exact r_reference308_checked
  · exact a_reference308_checked
  · exact r_fixed308_linked
  · exact a_fixed308_linked
  · exact time308_checked
  · exact ht
  · exact hw
theorem child_geometry308_checked : ReferenceWeightData.CoarseLowerShape.Batch0077.cert616.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0077.cert616.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0077.cert617.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0077.cert617.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights308 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0077.cert616∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch77_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0077.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0077.cert617∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch77_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0077.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0077.cert616.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0077.cert616.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0077.cert616.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry308_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights616_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0077.cert617.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0077.cert617.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry308_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry308_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights617_linked j (List.mem_finRange j))
theorem actual_frozen_frame308 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame308 (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.flow.timeParameter_mem child_geometry308_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights308 hz)
theorem r_profile309_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r309=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds := by rfl
theorem a_profile309_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a309=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a309.bounds := by rfl
theorem r_fixed309_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 7 := by decide +kernel
theorem a_fixed309_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a309.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.a309.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 9 := by decide +kernel
theorem ranks309_linked : ReferenceRankData.CoarseLowerShape.Batch0038.targetR309=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0038.targetA309=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 1 := by decide +kernel
theorem r_input309_linked : ReferenceRankData.CoarseLowerShape.Batch0038.r309.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds.gauge] := by decide +kernel
theorem a_input309_linked : ReferenceRankData.CoarseLowerShape.Batch0038.a309.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.a309.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.a309.bounds.gauge] := by decide +kernel
theorem geometry309_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.a := by decide +kernel
theorem weights618_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0077.cert618.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights619_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0077.cert619.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time309_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 10)=true := by decide +kernel
theorem r_reference309_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 0)=true := by decide +kernel
theorem a_reference309_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 1)=true := by decide +kernel
theorem rank_r_link309_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r309 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link309_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0038.a309.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a309 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints309 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell true ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r309 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile309_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link309_checked
    geometry309_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell false ReferenceProfileData.CoarseLowerShape.Batch0038.a309.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a309 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile309_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link309_checked
    geometry309_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks309_linked.1,←ranks309_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0038.r309.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a309.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0038.ordered309_checked hr ha ho
theorem frozen_frame309 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309 ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds ReferenceProfileData.CoarseLowerShape.Batch0038.a309.bounds
  · rw [←r_profile309_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile309_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry309_linked.2.2.2.2.1
  · exact geometry309_linked.2.2.2.2.2
  · exact r_reference309_checked
  · exact a_reference309_checked
  · exact r_fixed309_linked
  · exact a_fixed309_linked
  · exact time309_checked
  · exact ht
  · exact hw
theorem child_geometry309_checked : ReferenceWeightData.CoarseLowerShape.Batch0077.cert618.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0077.cert618.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0077.cert619.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0077.cert619.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights309 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0077.cert618∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch77_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0077.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0077.cert619∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch77_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0077.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0077.cert618.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0077.cert618.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0077.cert618.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry309_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights618_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0077.cert619.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0077.cert619.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry309_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry309_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights619_linked j (List.mem_finRange j))
theorem actual_frozen_frame309 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame309 (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.flow.timeParameter_mem child_geometry309_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights309 hz)
theorem r_profile310_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r310=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds := by rfl
theorem a_profile310_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a310=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a310.bounds := by rfl
theorem r_fixed310_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 7 := by decide +kernel
theorem a_fixed310_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a310.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.a310.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 9 := by decide +kernel
theorem ranks310_linked : ReferenceRankData.CoarseLowerShape.Batch0038.targetR310=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0038.targetA310=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 1 := by decide +kernel
theorem r_input310_linked : ReferenceRankData.CoarseLowerShape.Batch0038.r310.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds.gauge] := by decide +kernel
theorem a_input310_linked : ReferenceRankData.CoarseLowerShape.Batch0038.a310.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.a310.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.a310.bounds.gauge] := by decide +kernel
theorem geometry310_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.a := by decide +kernel
theorem weights620_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0077.cert620.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights621_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0077.cert621.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time310_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 10)=true := by decide +kernel
theorem r_reference310_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 0)=true := by decide +kernel
theorem a_reference310_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 1)=true := by decide +kernel
theorem rank_r_link310_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r310 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link310_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0038.a310.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a310 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints310 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell true ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r310 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile310_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link310_checked
    geometry310_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell false ReferenceProfileData.CoarseLowerShape.Batch0038.a310.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a310 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile310_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link310_checked
    geometry310_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks310_linked.1,←ranks310_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0038.r310.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a310.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0038.ordered310_checked hr ha ho
theorem frozen_frame310 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310 ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds ReferenceProfileData.CoarseLowerShape.Batch0038.a310.bounds
  · rw [←r_profile310_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile310_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry310_linked.2.2.2.2.1
  · exact geometry310_linked.2.2.2.2.2
  · exact r_reference310_checked
  · exact a_reference310_checked
  · exact r_fixed310_linked
  · exact a_fixed310_linked
  · exact time310_checked
  · exact ht
  · exact hw
theorem child_geometry310_checked : ReferenceWeightData.CoarseLowerShape.Batch0077.cert620.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0077.cert620.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0077.cert621.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0077.cert621.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights310 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0077.cert620∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch77_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0077.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0077.cert621∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch77_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0077.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0077.cert620.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0077.cert620.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0077.cert620.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry310_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights620_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0077.cert621.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0077.cert621.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry310_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry310_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights621_linked j (List.mem_finRange j))
theorem actual_frozen_frame310 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame310 (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.flow.timeParameter_mem child_geometry310_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights310 hz)
theorem r_profile311_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r311=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds := by rfl
theorem a_profile311_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a311=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a311.bounds := by rfl
theorem r_fixed311_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 7 := by decide +kernel
theorem a_fixed311_linked : ReferenceProfileData.CoarseLowerShape.Batch0038.a311.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0038.a311.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 9 := by decide +kernel
theorem ranks311_linked : ReferenceRankData.CoarseLowerShape.Batch0038.targetR311=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0038.targetA311=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 1 := by decide +kernel
theorem r_input311_linked : ReferenceRankData.CoarseLowerShape.Batch0038.r311.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds.gauge] := by decide +kernel
theorem a_input311_linked : ReferenceRankData.CoarseLowerShape.Batch0038.a311.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0038.a311.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0038.a311.bounds.gauge] := by decide +kernel
theorem geometry311_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.a := by decide +kernel
theorem weights622_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0077.cert622.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights623_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0077.cert623.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time311_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 10)=true := by decide +kernel
theorem r_reference311_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 0)=true := by decide +kernel
theorem a_reference311_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 1)=true := by decide +kernel
theorem rank_r_link311_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r311 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link311_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0038.a311.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a311 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints311 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell true ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds ReferenceRankData.CoarseLowerShape.Batch0038.r311 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile311_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link311_checked
    geometry311_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell false ReferenceProfileData.CoarseLowerShape.Batch0038.a311.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a311 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile311_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0038.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0038.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link311_checked
    geometry311_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks311_linked.1,←ranks311_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0038.r311.bounds ReferenceRankData.CoarseLowerShape.Batch0038.a311.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0038.ordered311_checked hr ha ho
theorem frozen_frame311 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311 ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds ReferenceProfileData.CoarseLowerShape.Batch0038.a311.bounds
  · rw [←r_profile311_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile311_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry311_linked.2.2.2.2.1
  · exact geometry311_linked.2.2.2.2.2
  · exact r_reference311_checked
  · exact a_reference311_checked
  · exact r_fixed311_linked
  · exact a_fixed311_linked
  · exact time311_checked
  · exact ht
  · exact hw
theorem child_geometry311_checked : ReferenceWeightData.CoarseLowerShape.Batch0077.cert622.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0077.cert622.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0077.cert623.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0077.cert623.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights311 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0077.cert622∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch77_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0077.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0077.cert623∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch77_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0077.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0077.cert622.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0077.cert622.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0077.cert622.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry311_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights622_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0077.cert623.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0077.cert623.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry311_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry311_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights623_linked j (List.mem_finRange j))
theorem actual_frozen_frame311 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame311 (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.flow.timeParameter_mem child_geometry311_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights311 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell304),(ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell305),(ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell306),(ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell307),(ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell308),(ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell309),(ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell310),(ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0038.cell311)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0038.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0038.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame304 hz
  · exact fun z hz=>actual_frozen_frame305 hz
  · exact fun z hz=>actual_frozen_frame306 hz
  · exact fun z hz=>actual_frozen_frame307 hz
  · exact fun z hz=>actual_frozen_frame308 hz
  · exact fun z hz=>actual_frozen_frame309 hz
  · exact fun z hz=>actual_frozen_frame310 hz
  · exact fun z hz=>actual_frozen_frame311 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints304 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints305 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints306 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints307 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints308 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints309 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints310 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints311 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry304_linked.1,geometry304_linked.2.1,geometry304_linked.2.2.1,geometry304_linked.2.2.2.1⟩
  · exact ⟨geometry305_linked.1,geometry305_linked.2.1,geometry305_linked.2.2.1,geometry305_linked.2.2.2.1⟩
  · exact ⟨geometry306_linked.1,geometry306_linked.2.1,geometry306_linked.2.2.1,geometry306_linked.2.2.2.1⟩
  · exact ⟨geometry307_linked.1,geometry307_linked.2.1,geometry307_linked.2.2.1,geometry307_linked.2.2.2.1⟩
  · exact ⟨geometry308_linked.1,geometry308_linked.2.1,geometry308_linked.2.2.1,geometry308_linked.2.2.2.1⟩
  · exact ⟨geometry309_linked.1,geometry309_linked.2.1,geometry309_linked.2.2.1,geometry309_linked.2.2.2.1⟩
  · exact ⟨geometry310_linked.1,geometry310_linked.2.1,geometry310_linked.2.2.1,geometry310_linked.2.2.2.1⟩
  · exact ⟨geometry311_linked.1,geometry311_linked.2.1,geometry311_linked.2.2.1,geometry311_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.a304.bounds,?_,geometry304_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a304.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile304_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds,?_,geometry304_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert304.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r304.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile304_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.a305.bounds,?_,geometry305_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a305.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile305_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds,?_,geometry305_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert305.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r305.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile305_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.a306.bounds,?_,geometry306_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a306.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile306_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds,?_,geometry306_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert306.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r306.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile306_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.a307.bounds,?_,geometry307_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a307.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile307_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds,?_,geometry307_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert307.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r307.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile307_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.a308.bounds,?_,geometry308_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a308.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile308_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds,?_,geometry308_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert308.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r308.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile308_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.a309.bounds,?_,geometry309_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a309.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile309_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds,?_,geometry309_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert309.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r309.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile309_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.a310.bounds,?_,geometry310_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a310.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile310_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds,?_,geometry310_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert310.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r310.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile310_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.a311.bounds,?_,geometry311_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0038.a311.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile311_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds,?_,geometry311_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0038.cert311.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0038.r311.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile311_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0038.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0038.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0038

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0039
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch78_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0078.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0078.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch79_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0079.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0079.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile312_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r312=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds := by rfl
theorem a_profile312_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a312=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a312.bounds := by rfl
theorem r_fixed312_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 7 := by decide +kernel
theorem a_fixed312_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a312.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.a312.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 9 := by decide +kernel
theorem ranks312_linked : ReferenceRankData.CoarseLowerShape.Batch0039.targetR312=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0039.targetA312=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 1 := by decide +kernel
theorem r_input312_linked : ReferenceRankData.CoarseLowerShape.Batch0039.r312.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds.gauge] := by decide +kernel
theorem a_input312_linked : ReferenceRankData.CoarseLowerShape.Batch0039.a312.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.a312.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.a312.bounds.gauge] := by decide +kernel
theorem geometry312_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.a := by decide +kernel
theorem weights624_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0078.cert624.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights625_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0078.cert625.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time312_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 10)=true := by decide +kernel
theorem r_reference312_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 0)=true := by decide +kernel
theorem a_reference312_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 1)=true := by decide +kernel
theorem rank_r_link312_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r312 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link312_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0039.a312.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a312 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints312 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell true ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r312 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile312_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link312_checked
    geometry312_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell false ReferenceProfileData.CoarseLowerShape.Batch0039.a312.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a312 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile312_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link312_checked
    geometry312_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks312_linked.1,←ranks312_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0039.r312.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a312.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0039.ordered312_checked hr ha ho
theorem frozen_frame312 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312 ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds ReferenceProfileData.CoarseLowerShape.Batch0039.a312.bounds
  · rw [←r_profile312_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile312_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry312_linked.2.2.2.2.1
  · exact geometry312_linked.2.2.2.2.2
  · exact r_reference312_checked
  · exact a_reference312_checked
  · exact r_fixed312_linked
  · exact a_fixed312_linked
  · exact time312_checked
  · exact ht
  · exact hw
theorem child_geometry312_checked : ReferenceWeightData.CoarseLowerShape.Batch0078.cert624.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0078.cert624.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0078.cert625.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0078.cert625.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights312 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0078.cert624∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch78_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0078.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0078.cert625∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch78_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0078.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0078.cert624.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0078.cert624.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0078.cert624.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry312_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights624_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0078.cert625.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0078.cert625.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry312_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry312_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights625_linked j (List.mem_finRange j))
theorem actual_frozen_frame312 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame312 (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.flow.timeParameter_mem child_geometry312_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights312 hz)
theorem r_profile313_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r313=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds := by rfl
theorem a_profile313_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a313=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a313.bounds := by rfl
theorem r_fixed313_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 7 := by decide +kernel
theorem a_fixed313_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a313.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.a313.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 9 := by decide +kernel
theorem ranks313_linked : ReferenceRankData.CoarseLowerShape.Batch0039.targetR313=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0039.targetA313=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 1 := by decide +kernel
theorem r_input313_linked : ReferenceRankData.CoarseLowerShape.Batch0039.r313.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds.gauge] := by decide +kernel
theorem a_input313_linked : ReferenceRankData.CoarseLowerShape.Batch0039.a313.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.a313.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.a313.bounds.gauge] := by decide +kernel
theorem geometry313_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.a := by decide +kernel
theorem weights626_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0078.cert626.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights627_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0078.cert627.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time313_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 10)=true := by decide +kernel
theorem r_reference313_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 0)=true := by decide +kernel
theorem a_reference313_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 1)=true := by decide +kernel
theorem rank_r_link313_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r313 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link313_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0039.a313.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a313 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints313 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell true ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r313 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile313_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link313_checked
    geometry313_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell false ReferenceProfileData.CoarseLowerShape.Batch0039.a313.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a313 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile313_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link313_checked
    geometry313_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks313_linked.1,←ranks313_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0039.r313.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a313.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0039.ordered313_checked hr ha ho
theorem frozen_frame313 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313 ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds ReferenceProfileData.CoarseLowerShape.Batch0039.a313.bounds
  · rw [←r_profile313_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile313_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry313_linked.2.2.2.2.1
  · exact geometry313_linked.2.2.2.2.2
  · exact r_reference313_checked
  · exact a_reference313_checked
  · exact r_fixed313_linked
  · exact a_fixed313_linked
  · exact time313_checked
  · exact ht
  · exact hw
theorem child_geometry313_checked : ReferenceWeightData.CoarseLowerShape.Batch0078.cert626.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0078.cert626.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0078.cert627.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0078.cert627.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights313 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0078.cert626∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch78_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0078.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0078.cert627∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch78_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0078.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0078.cert626.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0078.cert626.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0078.cert626.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry313_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights626_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0078.cert627.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0078.cert627.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry313_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry313_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights627_linked j (List.mem_finRange j))
theorem actual_frozen_frame313 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame313 (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.flow.timeParameter_mem child_geometry313_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights313 hz)
theorem r_profile314_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r314=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds := by rfl
theorem a_profile314_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a314=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a314.bounds := by rfl
theorem r_fixed314_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 7 := by decide +kernel
theorem a_fixed314_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a314.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.a314.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 9 := by decide +kernel
theorem ranks314_linked : ReferenceRankData.CoarseLowerShape.Batch0039.targetR314=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0039.targetA314=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 1 := by decide +kernel
theorem r_input314_linked : ReferenceRankData.CoarseLowerShape.Batch0039.r314.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds.gauge] := by decide +kernel
theorem a_input314_linked : ReferenceRankData.CoarseLowerShape.Batch0039.a314.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.a314.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.a314.bounds.gauge] := by decide +kernel
theorem geometry314_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.a := by decide +kernel
theorem weights628_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0078.cert628.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights629_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0078.cert629.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time314_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 10)=true := by decide +kernel
theorem r_reference314_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 0)=true := by decide +kernel
theorem a_reference314_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 1)=true := by decide +kernel
theorem rank_r_link314_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r314 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link314_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0039.a314.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a314 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints314 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell true ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r314 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile314_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link314_checked
    geometry314_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell false ReferenceProfileData.CoarseLowerShape.Batch0039.a314.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a314 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile314_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link314_checked
    geometry314_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks314_linked.1,←ranks314_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0039.r314.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a314.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0039.ordered314_checked hr ha ho
theorem frozen_frame314 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314 ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds ReferenceProfileData.CoarseLowerShape.Batch0039.a314.bounds
  · rw [←r_profile314_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile314_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry314_linked.2.2.2.2.1
  · exact geometry314_linked.2.2.2.2.2
  · exact r_reference314_checked
  · exact a_reference314_checked
  · exact r_fixed314_linked
  · exact a_fixed314_linked
  · exact time314_checked
  · exact ht
  · exact hw
theorem child_geometry314_checked : ReferenceWeightData.CoarseLowerShape.Batch0078.cert628.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0078.cert628.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0078.cert629.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0078.cert629.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights314 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0078.cert628∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch78_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0078.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0078.cert629∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch78_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0078.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0078.cert628.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0078.cert628.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0078.cert628.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry314_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights628_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0078.cert629.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0078.cert629.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry314_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry314_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights629_linked j (List.mem_finRange j))
theorem actual_frozen_frame314 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame314 (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.flow.timeParameter_mem child_geometry314_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights314 hz)
theorem r_profile315_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r315=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds := by rfl
theorem a_profile315_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a315=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a315.bounds := by rfl
theorem r_fixed315_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 7 := by decide +kernel
theorem a_fixed315_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a315.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.a315.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 9 := by decide +kernel
theorem ranks315_linked : ReferenceRankData.CoarseLowerShape.Batch0039.targetR315=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0039.targetA315=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 1 := by decide +kernel
theorem r_input315_linked : ReferenceRankData.CoarseLowerShape.Batch0039.r315.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds.gauge] := by decide +kernel
theorem a_input315_linked : ReferenceRankData.CoarseLowerShape.Batch0039.a315.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.a315.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.a315.bounds.gauge] := by decide +kernel
theorem geometry315_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.a := by decide +kernel
theorem weights630_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0078.cert630.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights631_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0078.cert631.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time315_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 10)=true := by decide +kernel
theorem r_reference315_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 0)=true := by decide +kernel
theorem a_reference315_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 1)=true := by decide +kernel
theorem rank_r_link315_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r315 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link315_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0039.a315.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a315 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints315 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell true ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r315 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile315_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link315_checked
    geometry315_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell false ReferenceProfileData.CoarseLowerShape.Batch0039.a315.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a315 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile315_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link315_checked
    geometry315_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks315_linked.1,←ranks315_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0039.r315.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a315.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0039.ordered315_checked hr ha ho
theorem frozen_frame315 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315 ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds ReferenceProfileData.CoarseLowerShape.Batch0039.a315.bounds
  · rw [←r_profile315_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile315_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry315_linked.2.2.2.2.1
  · exact geometry315_linked.2.2.2.2.2
  · exact r_reference315_checked
  · exact a_reference315_checked
  · exact r_fixed315_linked
  · exact a_fixed315_linked
  · exact time315_checked
  · exact ht
  · exact hw
theorem child_geometry315_checked : ReferenceWeightData.CoarseLowerShape.Batch0078.cert630.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0078.cert630.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0078.cert631.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0078.cert631.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights315 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0078.cert630∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch78_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0078.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0078.cert631∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch78_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0078.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0078.cert630.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0078.cert630.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0078.cert630.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry315_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights630_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0078.cert631.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0078.cert631.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry315_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry315_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights631_linked j (List.mem_finRange j))
theorem actual_frozen_frame315 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame315 (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.flow.timeParameter_mem child_geometry315_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights315 hz)
theorem r_profile316_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r316=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds := by rfl
theorem a_profile316_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a316=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a316.bounds := by rfl
theorem r_fixed316_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 7 := by decide +kernel
theorem a_fixed316_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a316.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.a316.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 9 := by decide +kernel
theorem ranks316_linked : ReferenceRankData.CoarseLowerShape.Batch0039.targetR316=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0039.targetA316=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 1 := by decide +kernel
theorem r_input316_linked : ReferenceRankData.CoarseLowerShape.Batch0039.r316.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds.gauge] := by decide +kernel
theorem a_input316_linked : ReferenceRankData.CoarseLowerShape.Batch0039.a316.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.a316.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.a316.bounds.gauge] := by decide +kernel
theorem geometry316_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.a := by decide +kernel
theorem weights632_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0079.cert632.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights633_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0079.cert633.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time316_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 10)=true := by decide +kernel
theorem r_reference316_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 0)=true := by decide +kernel
theorem a_reference316_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 1)=true := by decide +kernel
theorem rank_r_link316_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r316 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link316_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0039.a316.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a316 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints316 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell true ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r316 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile316_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link316_checked
    geometry316_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell false ReferenceProfileData.CoarseLowerShape.Batch0039.a316.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a316 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile316_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link316_checked
    geometry316_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks316_linked.1,←ranks316_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0039.r316.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a316.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0039.ordered316_checked hr ha ho
theorem frozen_frame316 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316 ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds ReferenceProfileData.CoarseLowerShape.Batch0039.a316.bounds
  · rw [←r_profile316_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile316_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry316_linked.2.2.2.2.1
  · exact geometry316_linked.2.2.2.2.2
  · exact r_reference316_checked
  · exact a_reference316_checked
  · exact r_fixed316_linked
  · exact a_fixed316_linked
  · exact time316_checked
  · exact ht
  · exact hw
theorem child_geometry316_checked : ReferenceWeightData.CoarseLowerShape.Batch0079.cert632.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0079.cert632.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0079.cert633.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0079.cert633.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights316 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0079.cert632∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch79_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0079.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0079.cert633∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch79_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0079.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0079.cert632.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0079.cert632.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0079.cert632.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry316_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights632_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0079.cert633.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0079.cert633.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry316_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry316_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights633_linked j (List.mem_finRange j))
theorem actual_frozen_frame316 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame316 (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.flow.timeParameter_mem child_geometry316_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights316 hz)
theorem r_profile317_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r317=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds := by rfl
theorem a_profile317_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a317=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a317.bounds := by rfl
theorem r_fixed317_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 7 := by decide +kernel
theorem a_fixed317_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a317.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.a317.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 9 := by decide +kernel
theorem ranks317_linked : ReferenceRankData.CoarseLowerShape.Batch0039.targetR317=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0039.targetA317=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 1 := by decide +kernel
theorem r_input317_linked : ReferenceRankData.CoarseLowerShape.Batch0039.r317.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds.gauge] := by decide +kernel
theorem a_input317_linked : ReferenceRankData.CoarseLowerShape.Batch0039.a317.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.a317.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.a317.bounds.gauge] := by decide +kernel
theorem geometry317_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.a := by decide +kernel
theorem weights634_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0079.cert634.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights635_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0079.cert635.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time317_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 10)=true := by decide +kernel
theorem r_reference317_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 0)=true := by decide +kernel
theorem a_reference317_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 1)=true := by decide +kernel
theorem rank_r_link317_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r317 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link317_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0039.a317.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a317 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints317 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell true ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r317 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile317_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link317_checked
    geometry317_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell false ReferenceProfileData.CoarseLowerShape.Batch0039.a317.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a317 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile317_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link317_checked
    geometry317_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks317_linked.1,←ranks317_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0039.r317.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a317.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0039.ordered317_checked hr ha ho
theorem frozen_frame317 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317 ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds ReferenceProfileData.CoarseLowerShape.Batch0039.a317.bounds
  · rw [←r_profile317_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile317_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry317_linked.2.2.2.2.1
  · exact geometry317_linked.2.2.2.2.2
  · exact r_reference317_checked
  · exact a_reference317_checked
  · exact r_fixed317_linked
  · exact a_fixed317_linked
  · exact time317_checked
  · exact ht
  · exact hw
theorem child_geometry317_checked : ReferenceWeightData.CoarseLowerShape.Batch0079.cert634.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0079.cert634.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0079.cert635.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0079.cert635.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights317 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0079.cert634∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch79_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0079.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0079.cert635∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch79_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0079.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0079.cert634.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0079.cert634.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0079.cert634.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry317_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights634_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0079.cert635.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0079.cert635.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry317_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry317_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights635_linked j (List.mem_finRange j))
theorem actual_frozen_frame317 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame317 (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.flow.timeParameter_mem child_geometry317_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights317 hz)
theorem r_profile318_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r318=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds := by rfl
theorem a_profile318_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a318=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a318.bounds := by rfl
theorem r_fixed318_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 7 := by decide +kernel
theorem a_fixed318_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a318.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.a318.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 9 := by decide +kernel
theorem ranks318_linked : ReferenceRankData.CoarseLowerShape.Batch0039.targetR318=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0039.targetA318=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 1 := by decide +kernel
theorem r_input318_linked : ReferenceRankData.CoarseLowerShape.Batch0039.r318.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds.gauge] := by decide +kernel
theorem a_input318_linked : ReferenceRankData.CoarseLowerShape.Batch0039.a318.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.a318.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.a318.bounds.gauge] := by decide +kernel
theorem geometry318_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.a := by decide +kernel
theorem weights636_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0079.cert636.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights637_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0079.cert637.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time318_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 10)=true := by decide +kernel
theorem r_reference318_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 0)=true := by decide +kernel
theorem a_reference318_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 1)=true := by decide +kernel
theorem rank_r_link318_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r318 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link318_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0039.a318.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a318 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints318 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell true ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r318 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile318_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link318_checked
    geometry318_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell false ReferenceProfileData.CoarseLowerShape.Batch0039.a318.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a318 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile318_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link318_checked
    geometry318_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks318_linked.1,←ranks318_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0039.r318.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a318.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0039.ordered318_checked hr ha ho
theorem frozen_frame318 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318 ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds ReferenceProfileData.CoarseLowerShape.Batch0039.a318.bounds
  · rw [←r_profile318_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile318_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry318_linked.2.2.2.2.1
  · exact geometry318_linked.2.2.2.2.2
  · exact r_reference318_checked
  · exact a_reference318_checked
  · exact r_fixed318_linked
  · exact a_fixed318_linked
  · exact time318_checked
  · exact ht
  · exact hw
theorem child_geometry318_checked : ReferenceWeightData.CoarseLowerShape.Batch0079.cert636.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0079.cert636.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0079.cert637.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0079.cert637.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights318 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0079.cert636∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch79_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0079.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0079.cert637∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch79_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0079.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0079.cert636.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0079.cert636.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0079.cert636.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry318_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights636_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0079.cert637.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0079.cert637.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry318_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry318_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights637_linked j (List.mem_finRange j))
theorem actual_frozen_frame318 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame318 (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.flow.timeParameter_mem child_geometry318_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights318 hz)
theorem r_profile319_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r319=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds := by rfl
theorem a_profile319_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a319=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a319.bounds := by rfl
theorem r_fixed319_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 7 := by decide +kernel
theorem a_fixed319_linked : ReferenceProfileData.CoarseLowerShape.Batch0039.a319.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0039.a319.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 9 := by decide +kernel
theorem ranks319_linked : ReferenceRankData.CoarseLowerShape.Batch0039.targetR319=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0039.targetA319=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 1 := by decide +kernel
theorem r_input319_linked : ReferenceRankData.CoarseLowerShape.Batch0039.r319.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds.gauge] := by decide +kernel
theorem a_input319_linked : ReferenceRankData.CoarseLowerShape.Batch0039.a319.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0039.a319.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0039.a319.bounds.gauge] := by decide +kernel
theorem geometry319_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.a := by decide +kernel
theorem weights638_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0079.cert638.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights639_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0079.cert639.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time319_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 10)=true := by decide +kernel
theorem r_reference319_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 0)=true := by decide +kernel
theorem a_reference319_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 1)=true := by decide +kernel
theorem rank_r_link319_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r319 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link319_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0039.a319.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a319 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints319 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell true ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds ReferenceRankData.CoarseLowerShape.Batch0039.r319 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile319_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link319_checked
    geometry319_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell false ReferenceProfileData.CoarseLowerShape.Batch0039.a319.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a319 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile319_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0039.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0039.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link319_checked
    geometry319_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks319_linked.1,←ranks319_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0039.r319.bounds ReferenceRankData.CoarseLowerShape.Batch0039.a319.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0039.ordered319_checked hr ha ho
theorem frozen_frame319 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319 ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds ReferenceProfileData.CoarseLowerShape.Batch0039.a319.bounds
  · rw [←r_profile319_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile319_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry319_linked.2.2.2.2.1
  · exact geometry319_linked.2.2.2.2.2
  · exact r_reference319_checked
  · exact a_reference319_checked
  · exact r_fixed319_linked
  · exact a_fixed319_linked
  · exact time319_checked
  · exact ht
  · exact hw
theorem child_geometry319_checked : ReferenceWeightData.CoarseLowerShape.Batch0079.cert638.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0079.cert638.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0079.cert639.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0079.cert639.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights319 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0079.cert638∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch79_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0079.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0079.cert639∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch79_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0079.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0079.cert638.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0079.cert638.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0079.cert638.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry319_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights638_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0079.cert639.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0079.cert639.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry319_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry319_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights639_linked j (List.mem_finRange j))
theorem actual_frozen_frame319 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame319 (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.flow.timeParameter_mem child_geometry319_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights319 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell312),(ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell313),(ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell314),(ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell315),(ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell316),(ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell317),(ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell318),(ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0039.cell319)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0039.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0039.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame312 hz
  · exact fun z hz=>actual_frozen_frame313 hz
  · exact fun z hz=>actual_frozen_frame314 hz
  · exact fun z hz=>actual_frozen_frame315 hz
  · exact fun z hz=>actual_frozen_frame316 hz
  · exact fun z hz=>actual_frozen_frame317 hz
  · exact fun z hz=>actual_frozen_frame318 hz
  · exact fun z hz=>actual_frozen_frame319 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints312 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints313 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints314 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints315 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints316 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints317 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints318 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints319 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry312_linked.1,geometry312_linked.2.1,geometry312_linked.2.2.1,geometry312_linked.2.2.2.1⟩
  · exact ⟨geometry313_linked.1,geometry313_linked.2.1,geometry313_linked.2.2.1,geometry313_linked.2.2.2.1⟩
  · exact ⟨geometry314_linked.1,geometry314_linked.2.1,geometry314_linked.2.2.1,geometry314_linked.2.2.2.1⟩
  · exact ⟨geometry315_linked.1,geometry315_linked.2.1,geometry315_linked.2.2.1,geometry315_linked.2.2.2.1⟩
  · exact ⟨geometry316_linked.1,geometry316_linked.2.1,geometry316_linked.2.2.1,geometry316_linked.2.2.2.1⟩
  · exact ⟨geometry317_linked.1,geometry317_linked.2.1,geometry317_linked.2.2.1,geometry317_linked.2.2.2.1⟩
  · exact ⟨geometry318_linked.1,geometry318_linked.2.1,geometry318_linked.2.2.1,geometry318_linked.2.2.2.1⟩
  · exact ⟨geometry319_linked.1,geometry319_linked.2.1,geometry319_linked.2.2.1,geometry319_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.a312.bounds,?_,geometry312_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a312.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile312_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds,?_,geometry312_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert312.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r312.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile312_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.a313.bounds,?_,geometry313_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a313.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile313_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds,?_,geometry313_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert313.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r313.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile313_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.a314.bounds,?_,geometry314_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a314.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile314_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds,?_,geometry314_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert314.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r314.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile314_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.a315.bounds,?_,geometry315_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a315.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile315_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds,?_,geometry315_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert315.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r315.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile315_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.a316.bounds,?_,geometry316_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a316.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile316_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds,?_,geometry316_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert316.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r316.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile316_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.a317.bounds,?_,geometry317_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a317.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile317_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds,?_,geometry317_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert317.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r317.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile317_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.a318.bounds,?_,geometry318_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a318.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile318_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds,?_,geometry318_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert318.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r318.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile318_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.a319.bounds,?_,geometry319_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0039.a319.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile319_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds,?_,geometry319_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0039.cert319.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0039.r319.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile319_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0039.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0039.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0039
