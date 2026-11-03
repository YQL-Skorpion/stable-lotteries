import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0021_0024
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0021_0024
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0049_0052
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0022_0025
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0023_0026
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Bundle0020_0023
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0025_0028
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0025_0028
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0053_0056
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0026_0029
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0027_0030

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0024
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch48_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0048.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0048.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch49_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0049.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0049.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile192_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r192=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds := by rfl
theorem a_profile192_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a192=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a192.bounds := by rfl
theorem r_fixed192_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 7 := by decide +kernel
theorem a_fixed192_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a192.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.a192.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 9 := by decide +kernel
theorem ranks192_linked : ReferenceRankData.CoarseLowerShape.Batch0024.targetR192=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0024.targetA192=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 1 := by decide +kernel
theorem r_input192_linked : ReferenceRankData.CoarseLowerShape.Batch0024.r192.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds.gauge] := by decide +kernel
theorem a_input192_linked : ReferenceRankData.CoarseLowerShape.Batch0024.a192.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.a192.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.a192.bounds.gauge] := by decide +kernel
theorem geometry192_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.a := by decide +kernel
theorem weights384_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0048.cert384.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights385_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0048.cert385.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time192_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 10)=true := by decide +kernel
theorem r_reference192_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 0)=true := by decide +kernel
theorem a_reference192_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 1)=true := by decide +kernel
theorem rank_r_link192_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r192 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link192_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0024.a192.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a192 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints192 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell true ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r192 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile192_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link192_checked
    geometry192_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell false ReferenceProfileData.CoarseLowerShape.Batch0024.a192.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a192 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile192_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link192_checked
    geometry192_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks192_linked.1,←ranks192_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0024.r192.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a192.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0024.ordered192_checked hr ha ho
theorem frozen_frame192 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192 ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds ReferenceProfileData.CoarseLowerShape.Batch0024.a192.bounds
  · rw [←r_profile192_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile192_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry192_linked.2.2.2.2.1
  · exact geometry192_linked.2.2.2.2.2
  · exact r_reference192_checked
  · exact a_reference192_checked
  · exact r_fixed192_linked
  · exact a_fixed192_linked
  · exact time192_checked
  · exact ht
  · exact hw
theorem child_geometry192_checked : ReferenceWeightData.CoarseLowerShape.Batch0048.cert384.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0048.cert384.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0048.cert385.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0048.cert385.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights192 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0048.cert384∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch48_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0048.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0048.cert385∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch48_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0048.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0048.cert384.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0048.cert384.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0048.cert384.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry192_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights384_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0048.cert385.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0048.cert385.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry192_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry192_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights385_linked j (List.mem_finRange j))
theorem actual_frozen_frame192 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame192 (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.flow.timeParameter_mem child_geometry192_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights192 hz)
theorem r_profile193_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r193=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds := by rfl
theorem a_profile193_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a193=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a193.bounds := by rfl
theorem r_fixed193_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 7 := by decide +kernel
theorem a_fixed193_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a193.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.a193.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 9 := by decide +kernel
theorem ranks193_linked : ReferenceRankData.CoarseLowerShape.Batch0024.targetR193=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0024.targetA193=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 1 := by decide +kernel
theorem r_input193_linked : ReferenceRankData.CoarseLowerShape.Batch0024.r193.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds.gauge] := by decide +kernel
theorem a_input193_linked : ReferenceRankData.CoarseLowerShape.Batch0024.a193.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.a193.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.a193.bounds.gauge] := by decide +kernel
theorem geometry193_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.a := by decide +kernel
theorem weights386_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0048.cert386.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights387_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0048.cert387.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time193_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 10)=true := by decide +kernel
theorem r_reference193_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 0)=true := by decide +kernel
theorem a_reference193_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 1)=true := by decide +kernel
theorem rank_r_link193_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r193 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link193_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0024.a193.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a193 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints193 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell true ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r193 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile193_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link193_checked
    geometry193_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell false ReferenceProfileData.CoarseLowerShape.Batch0024.a193.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a193 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile193_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link193_checked
    geometry193_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks193_linked.1,←ranks193_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0024.r193.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a193.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0024.ordered193_checked hr ha ho
theorem frozen_frame193 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193 ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds ReferenceProfileData.CoarseLowerShape.Batch0024.a193.bounds
  · rw [←r_profile193_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile193_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry193_linked.2.2.2.2.1
  · exact geometry193_linked.2.2.2.2.2
  · exact r_reference193_checked
  · exact a_reference193_checked
  · exact r_fixed193_linked
  · exact a_fixed193_linked
  · exact time193_checked
  · exact ht
  · exact hw
theorem child_geometry193_checked : ReferenceWeightData.CoarseLowerShape.Batch0048.cert386.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0048.cert386.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0048.cert387.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0048.cert387.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights193 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0048.cert386∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch48_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0048.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0048.cert387∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch48_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0048.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0048.cert386.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0048.cert386.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0048.cert386.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry193_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights386_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0048.cert387.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0048.cert387.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry193_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry193_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights387_linked j (List.mem_finRange j))
theorem actual_frozen_frame193 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame193 (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.flow.timeParameter_mem child_geometry193_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights193 hz)
theorem r_profile194_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r194=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds := by rfl
theorem a_profile194_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a194=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a194.bounds := by rfl
theorem r_fixed194_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 7 := by decide +kernel
theorem a_fixed194_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a194.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.a194.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 9 := by decide +kernel
theorem ranks194_linked : ReferenceRankData.CoarseLowerShape.Batch0024.targetR194=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0024.targetA194=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 1 := by decide +kernel
theorem r_input194_linked : ReferenceRankData.CoarseLowerShape.Batch0024.r194.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds.gauge] := by decide +kernel
theorem a_input194_linked : ReferenceRankData.CoarseLowerShape.Batch0024.a194.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.a194.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.a194.bounds.gauge] := by decide +kernel
theorem geometry194_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.a := by decide +kernel
theorem weights388_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0048.cert388.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights389_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0048.cert389.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time194_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 10)=true := by decide +kernel
theorem r_reference194_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 0)=true := by decide +kernel
theorem a_reference194_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 1)=true := by decide +kernel
theorem rank_r_link194_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r194 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link194_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0024.a194.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a194 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints194 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell true ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r194 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile194_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link194_checked
    geometry194_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell false ReferenceProfileData.CoarseLowerShape.Batch0024.a194.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a194 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile194_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link194_checked
    geometry194_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks194_linked.1,←ranks194_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0024.r194.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a194.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0024.ordered194_checked hr ha ho
theorem frozen_frame194 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194 ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds ReferenceProfileData.CoarseLowerShape.Batch0024.a194.bounds
  · rw [←r_profile194_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile194_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry194_linked.2.2.2.2.1
  · exact geometry194_linked.2.2.2.2.2
  · exact r_reference194_checked
  · exact a_reference194_checked
  · exact r_fixed194_linked
  · exact a_fixed194_linked
  · exact time194_checked
  · exact ht
  · exact hw
theorem child_geometry194_checked : ReferenceWeightData.CoarseLowerShape.Batch0048.cert388.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0048.cert388.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0048.cert389.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0048.cert389.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights194 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0048.cert388∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch48_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0048.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0048.cert389∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch48_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0048.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0048.cert388.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0048.cert388.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0048.cert388.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry194_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights388_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0048.cert389.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0048.cert389.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry194_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry194_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights389_linked j (List.mem_finRange j))
theorem actual_frozen_frame194 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame194 (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.flow.timeParameter_mem child_geometry194_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights194 hz)
theorem r_profile195_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r195=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds := by rfl
theorem a_profile195_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a195=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a195.bounds := by rfl
theorem r_fixed195_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 7 := by decide +kernel
theorem a_fixed195_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a195.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.a195.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 9 := by decide +kernel
theorem ranks195_linked : ReferenceRankData.CoarseLowerShape.Batch0024.targetR195=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0024.targetA195=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 1 := by decide +kernel
theorem r_input195_linked : ReferenceRankData.CoarseLowerShape.Batch0024.r195.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds.gauge] := by decide +kernel
theorem a_input195_linked : ReferenceRankData.CoarseLowerShape.Batch0024.a195.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.a195.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.a195.bounds.gauge] := by decide +kernel
theorem geometry195_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.a := by decide +kernel
theorem weights390_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0048.cert390.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights391_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0048.cert391.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time195_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 10)=true := by decide +kernel
theorem r_reference195_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 0)=true := by decide +kernel
theorem a_reference195_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 1)=true := by decide +kernel
theorem rank_r_link195_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r195 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link195_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0024.a195.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a195 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints195 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell true ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r195 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile195_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link195_checked
    geometry195_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell false ReferenceProfileData.CoarseLowerShape.Batch0024.a195.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a195 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile195_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link195_checked
    geometry195_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks195_linked.1,←ranks195_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0024.r195.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a195.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0024.ordered195_checked hr ha ho
theorem frozen_frame195 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195 ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds ReferenceProfileData.CoarseLowerShape.Batch0024.a195.bounds
  · rw [←r_profile195_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile195_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry195_linked.2.2.2.2.1
  · exact geometry195_linked.2.2.2.2.2
  · exact r_reference195_checked
  · exact a_reference195_checked
  · exact r_fixed195_linked
  · exact a_fixed195_linked
  · exact time195_checked
  · exact ht
  · exact hw
theorem child_geometry195_checked : ReferenceWeightData.CoarseLowerShape.Batch0048.cert390.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0048.cert390.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0048.cert391.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0048.cert391.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights195 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0048.cert390∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch48_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0048.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0048.cert391∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch48_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0048.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0048.cert390.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0048.cert390.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0048.cert390.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry195_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights390_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0048.cert391.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0048.cert391.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry195_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry195_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights391_linked j (List.mem_finRange j))
theorem actual_frozen_frame195 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame195 (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.flow.timeParameter_mem child_geometry195_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights195 hz)
theorem r_profile196_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r196=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds := by rfl
theorem a_profile196_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a196=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a196.bounds := by rfl
theorem r_fixed196_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 7 := by decide +kernel
theorem a_fixed196_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a196.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.a196.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 9 := by decide +kernel
theorem ranks196_linked : ReferenceRankData.CoarseLowerShape.Batch0024.targetR196=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0024.targetA196=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 1 := by decide +kernel
theorem r_input196_linked : ReferenceRankData.CoarseLowerShape.Batch0024.r196.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds.gauge] := by decide +kernel
theorem a_input196_linked : ReferenceRankData.CoarseLowerShape.Batch0024.a196.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.a196.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.a196.bounds.gauge] := by decide +kernel
theorem geometry196_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.a := by decide +kernel
theorem weights392_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0049.cert392.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights393_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0049.cert393.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time196_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 10)=true := by decide +kernel
theorem r_reference196_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 0)=true := by decide +kernel
theorem a_reference196_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 1)=true := by decide +kernel
theorem rank_r_link196_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r196 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link196_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0024.a196.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a196 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints196 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell true ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r196 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile196_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link196_checked
    geometry196_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell false ReferenceProfileData.CoarseLowerShape.Batch0024.a196.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a196 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile196_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link196_checked
    geometry196_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks196_linked.1,←ranks196_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0024.r196.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a196.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0024.ordered196_checked hr ha ho
theorem frozen_frame196 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196 ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds ReferenceProfileData.CoarseLowerShape.Batch0024.a196.bounds
  · rw [←r_profile196_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile196_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry196_linked.2.2.2.2.1
  · exact geometry196_linked.2.2.2.2.2
  · exact r_reference196_checked
  · exact a_reference196_checked
  · exact r_fixed196_linked
  · exact a_fixed196_linked
  · exact time196_checked
  · exact ht
  · exact hw
theorem child_geometry196_checked : ReferenceWeightData.CoarseLowerShape.Batch0049.cert392.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0049.cert392.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0049.cert393.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0049.cert393.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights196 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0049.cert392∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch49_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0049.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0049.cert393∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch49_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0049.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0049.cert392.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0049.cert392.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0049.cert392.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry196_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights392_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0049.cert393.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0049.cert393.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry196_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry196_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights393_linked j (List.mem_finRange j))
theorem actual_frozen_frame196 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame196 (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.flow.timeParameter_mem child_geometry196_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights196 hz)
theorem r_profile197_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r197=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds := by rfl
theorem a_profile197_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a197=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a197.bounds := by rfl
theorem r_fixed197_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 7 := by decide +kernel
theorem a_fixed197_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a197.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.a197.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 9 := by decide +kernel
theorem ranks197_linked : ReferenceRankData.CoarseLowerShape.Batch0024.targetR197=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0024.targetA197=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 1 := by decide +kernel
theorem r_input197_linked : ReferenceRankData.CoarseLowerShape.Batch0024.r197.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds.gauge] := by decide +kernel
theorem a_input197_linked : ReferenceRankData.CoarseLowerShape.Batch0024.a197.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.a197.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.a197.bounds.gauge] := by decide +kernel
theorem geometry197_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.a := by decide +kernel
theorem weights394_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0049.cert394.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights395_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0049.cert395.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time197_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 10)=true := by decide +kernel
theorem r_reference197_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 0)=true := by decide +kernel
theorem a_reference197_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 1)=true := by decide +kernel
theorem rank_r_link197_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r197 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link197_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0024.a197.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a197 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints197 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell true ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r197 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile197_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link197_checked
    geometry197_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell false ReferenceProfileData.CoarseLowerShape.Batch0024.a197.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a197 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile197_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link197_checked
    geometry197_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks197_linked.1,←ranks197_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0024.r197.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a197.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0024.ordered197_checked hr ha ho
theorem frozen_frame197 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197 ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds ReferenceProfileData.CoarseLowerShape.Batch0024.a197.bounds
  · rw [←r_profile197_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile197_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry197_linked.2.2.2.2.1
  · exact geometry197_linked.2.2.2.2.2
  · exact r_reference197_checked
  · exact a_reference197_checked
  · exact r_fixed197_linked
  · exact a_fixed197_linked
  · exact time197_checked
  · exact ht
  · exact hw
theorem child_geometry197_checked : ReferenceWeightData.CoarseLowerShape.Batch0049.cert394.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0049.cert394.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0049.cert395.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0049.cert395.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights197 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0049.cert394∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch49_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0049.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0049.cert395∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch49_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0049.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0049.cert394.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0049.cert394.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0049.cert394.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry197_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights394_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0049.cert395.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0049.cert395.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry197_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry197_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights395_linked j (List.mem_finRange j))
theorem actual_frozen_frame197 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame197 (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.flow.timeParameter_mem child_geometry197_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights197 hz)
theorem r_profile198_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r198=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds := by rfl
theorem a_profile198_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a198=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a198.bounds := by rfl
theorem r_fixed198_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 7 := by decide +kernel
theorem a_fixed198_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a198.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.a198.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 9 := by decide +kernel
theorem ranks198_linked : ReferenceRankData.CoarseLowerShape.Batch0024.targetR198=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0024.targetA198=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 1 := by decide +kernel
theorem r_input198_linked : ReferenceRankData.CoarseLowerShape.Batch0024.r198.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds.gauge] := by decide +kernel
theorem a_input198_linked : ReferenceRankData.CoarseLowerShape.Batch0024.a198.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.a198.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.a198.bounds.gauge] := by decide +kernel
theorem geometry198_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.a := by decide +kernel
theorem weights396_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0049.cert396.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights397_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0049.cert397.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time198_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 10)=true := by decide +kernel
theorem r_reference198_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 0)=true := by decide +kernel
theorem a_reference198_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 1)=true := by decide +kernel
theorem rank_r_link198_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r198 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link198_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0024.a198.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a198 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints198 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell true ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r198 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile198_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link198_checked
    geometry198_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell false ReferenceProfileData.CoarseLowerShape.Batch0024.a198.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a198 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile198_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link198_checked
    geometry198_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks198_linked.1,←ranks198_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0024.r198.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a198.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0024.ordered198_checked hr ha ho
theorem frozen_frame198 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198 ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds ReferenceProfileData.CoarseLowerShape.Batch0024.a198.bounds
  · rw [←r_profile198_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile198_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry198_linked.2.2.2.2.1
  · exact geometry198_linked.2.2.2.2.2
  · exact r_reference198_checked
  · exact a_reference198_checked
  · exact r_fixed198_linked
  · exact a_fixed198_linked
  · exact time198_checked
  · exact ht
  · exact hw
theorem child_geometry198_checked : ReferenceWeightData.CoarseLowerShape.Batch0049.cert396.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0049.cert396.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0049.cert397.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0049.cert397.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights198 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0049.cert396∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch49_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0049.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0049.cert397∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch49_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0049.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0049.cert396.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0049.cert396.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0049.cert396.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry198_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights396_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0049.cert397.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0049.cert397.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry198_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry198_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights397_linked j (List.mem_finRange j))
theorem actual_frozen_frame198 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame198 (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.flow.timeParameter_mem child_geometry198_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights198 hz)
theorem r_profile199_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r199=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds := by rfl
theorem a_profile199_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a199=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a199.bounds := by rfl
theorem r_fixed199_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 7 := by decide +kernel
theorem a_fixed199_linked : ReferenceProfileData.CoarseLowerShape.Batch0024.a199.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0024.a199.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 9 := by decide +kernel
theorem ranks199_linked : ReferenceRankData.CoarseLowerShape.Batch0024.targetR199=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0024.targetA199=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 1 := by decide +kernel
theorem r_input199_linked : ReferenceRankData.CoarseLowerShape.Batch0024.r199.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds.gauge] := by decide +kernel
theorem a_input199_linked : ReferenceRankData.CoarseLowerShape.Batch0024.a199.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0024.a199.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0024.a199.bounds.gauge] := by decide +kernel
theorem geometry199_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.a := by decide +kernel
theorem weights398_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0049.cert398.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights399_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0049.cert399.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time199_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 10)=true := by decide +kernel
theorem r_reference199_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 0)=true := by decide +kernel
theorem a_reference199_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 1)=true := by decide +kernel
theorem rank_r_link199_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r199 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link199_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0024.a199.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a199 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints199 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell true ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds ReferenceRankData.CoarseLowerShape.Batch0024.r199 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile199_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link199_checked
    geometry199_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell false ReferenceProfileData.CoarseLowerShape.Batch0024.a199.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a199 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile199_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0024.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0024.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link199_checked
    geometry199_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks199_linked.1,←ranks199_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0024.r199.bounds ReferenceRankData.CoarseLowerShape.Batch0024.a199.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0024.ordered199_checked hr ha ho
theorem frozen_frame199 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199 ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds ReferenceProfileData.CoarseLowerShape.Batch0024.a199.bounds
  · rw [←r_profile199_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile199_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry199_linked.2.2.2.2.1
  · exact geometry199_linked.2.2.2.2.2
  · exact r_reference199_checked
  · exact a_reference199_checked
  · exact r_fixed199_linked
  · exact a_fixed199_linked
  · exact time199_checked
  · exact ht
  · exact hw
theorem child_geometry199_checked : ReferenceWeightData.CoarseLowerShape.Batch0049.cert398.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0049.cert398.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0049.cert399.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0049.cert399.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights199 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0049.cert398∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch49_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0049.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0049.cert399∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch49_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0049.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0049.cert398.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0049.cert398.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0049.cert398.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry199_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights398_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0049.cert399.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0049.cert399.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry199_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry199_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights399_linked j (List.mem_finRange j))
theorem actual_frozen_frame199 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame199 (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.flow.timeParameter_mem child_geometry199_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights199 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell192),(ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell193),(ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell194),(ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell195),(ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell196),(ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell197),(ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell198),(ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0024.cell199)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0024.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0024.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame192 hz
  · exact fun z hz=>actual_frozen_frame193 hz
  · exact fun z hz=>actual_frozen_frame194 hz
  · exact fun z hz=>actual_frozen_frame195 hz
  · exact fun z hz=>actual_frozen_frame196 hz
  · exact fun z hz=>actual_frozen_frame197 hz
  · exact fun z hz=>actual_frozen_frame198 hz
  · exact fun z hz=>actual_frozen_frame199 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints192 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints193 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints194 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints195 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints196 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints197 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints198 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints199 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry192_linked.1,geometry192_linked.2.1,geometry192_linked.2.2.1,geometry192_linked.2.2.2.1⟩
  · exact ⟨geometry193_linked.1,geometry193_linked.2.1,geometry193_linked.2.2.1,geometry193_linked.2.2.2.1⟩
  · exact ⟨geometry194_linked.1,geometry194_linked.2.1,geometry194_linked.2.2.1,geometry194_linked.2.2.2.1⟩
  · exact ⟨geometry195_linked.1,geometry195_linked.2.1,geometry195_linked.2.2.1,geometry195_linked.2.2.2.1⟩
  · exact ⟨geometry196_linked.1,geometry196_linked.2.1,geometry196_linked.2.2.1,geometry196_linked.2.2.2.1⟩
  · exact ⟨geometry197_linked.1,geometry197_linked.2.1,geometry197_linked.2.2.1,geometry197_linked.2.2.2.1⟩
  · exact ⟨geometry198_linked.1,geometry198_linked.2.1,geometry198_linked.2.2.1,geometry198_linked.2.2.2.1⟩
  · exact ⟨geometry199_linked.1,geometry199_linked.2.1,geometry199_linked.2.2.1,geometry199_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.a192.bounds,?_,geometry192_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a192.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile192_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds,?_,geometry192_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert192.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r192.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile192_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.a193.bounds,?_,geometry193_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a193.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile193_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds,?_,geometry193_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert193.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r193.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile193_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.a194.bounds,?_,geometry194_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a194.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile194_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds,?_,geometry194_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert194.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r194.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile194_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.a195.bounds,?_,geometry195_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a195.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile195_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds,?_,geometry195_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert195.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r195.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile195_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.a196.bounds,?_,geometry196_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a196.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile196_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds,?_,geometry196_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert196.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r196.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile196_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.a197.bounds,?_,geometry197_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a197.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile197_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds,?_,geometry197_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert197.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r197.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile197_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.a198.bounds,?_,geometry198_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a198.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile198_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds,?_,geometry198_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert198.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r198.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile198_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.a199.bounds,?_,geometry199_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0024.a199.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile199_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds,?_,geometry199_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0024.cert199.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0024.r199.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile199_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0024.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0024.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0024

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0025
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch50_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0050.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0050.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch51_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0051.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0051.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile200_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r200=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds := by rfl
theorem a_profile200_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a200=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a200.bounds := by rfl
theorem r_fixed200_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 7 := by decide +kernel
theorem a_fixed200_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a200.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.a200.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 9 := by decide +kernel
theorem ranks200_linked : ReferenceRankData.CoarseLowerShape.Batch0025.targetR200=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0025.targetA200=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 1 := by decide +kernel
theorem r_input200_linked : ReferenceRankData.CoarseLowerShape.Batch0025.r200.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds.gauge] := by decide +kernel
theorem a_input200_linked : ReferenceRankData.CoarseLowerShape.Batch0025.a200.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.a200.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.a200.bounds.gauge] := by decide +kernel
theorem geometry200_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.a := by decide +kernel
theorem weights400_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0050.cert400.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights401_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0050.cert401.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time200_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 10)=true := by decide +kernel
theorem r_reference200_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 0)=true := by decide +kernel
theorem a_reference200_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 1)=true := by decide +kernel
theorem rank_r_link200_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r200 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link200_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0025.a200.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a200 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints200 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell true ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r200 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile200_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link200_checked
    geometry200_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell false ReferenceProfileData.CoarseLowerShape.Batch0025.a200.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a200 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile200_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link200_checked
    geometry200_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks200_linked.1,←ranks200_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0025.r200.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a200.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0025.ordered200_checked hr ha ho
theorem frozen_frame200 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200 ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds ReferenceProfileData.CoarseLowerShape.Batch0025.a200.bounds
  · rw [←r_profile200_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile200_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry200_linked.2.2.2.2.1
  · exact geometry200_linked.2.2.2.2.2
  · exact r_reference200_checked
  · exact a_reference200_checked
  · exact r_fixed200_linked
  · exact a_fixed200_linked
  · exact time200_checked
  · exact ht
  · exact hw
theorem child_geometry200_checked : ReferenceWeightData.CoarseLowerShape.Batch0050.cert400.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0050.cert400.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0050.cert401.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0050.cert401.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights200 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0050.cert400∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch50_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0050.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0050.cert401∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch50_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0050.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0050.cert400.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0050.cert400.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0050.cert400.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry200_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights400_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0050.cert401.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0050.cert401.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry200_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry200_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights401_linked j (List.mem_finRange j))
theorem actual_frozen_frame200 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame200 (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.flow.timeParameter_mem child_geometry200_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights200 hz)
theorem r_profile201_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r201=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds := by rfl
theorem a_profile201_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a201=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a201.bounds := by rfl
theorem r_fixed201_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 7 := by decide +kernel
theorem a_fixed201_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a201.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.a201.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 9 := by decide +kernel
theorem ranks201_linked : ReferenceRankData.CoarseLowerShape.Batch0025.targetR201=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0025.targetA201=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 1 := by decide +kernel
theorem r_input201_linked : ReferenceRankData.CoarseLowerShape.Batch0025.r201.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds.gauge] := by decide +kernel
theorem a_input201_linked : ReferenceRankData.CoarseLowerShape.Batch0025.a201.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.a201.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.a201.bounds.gauge] := by decide +kernel
theorem geometry201_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.a := by decide +kernel
theorem weights402_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0050.cert402.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights403_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0050.cert403.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time201_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 10)=true := by decide +kernel
theorem r_reference201_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 0)=true := by decide +kernel
theorem a_reference201_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 1)=true := by decide +kernel
theorem rank_r_link201_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r201 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link201_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0025.a201.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a201 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints201 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell true ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r201 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile201_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link201_checked
    geometry201_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell false ReferenceProfileData.CoarseLowerShape.Batch0025.a201.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a201 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile201_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link201_checked
    geometry201_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks201_linked.1,←ranks201_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0025.r201.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a201.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0025.ordered201_checked hr ha ho
theorem frozen_frame201 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201 ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds ReferenceProfileData.CoarseLowerShape.Batch0025.a201.bounds
  · rw [←r_profile201_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile201_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry201_linked.2.2.2.2.1
  · exact geometry201_linked.2.2.2.2.2
  · exact r_reference201_checked
  · exact a_reference201_checked
  · exact r_fixed201_linked
  · exact a_fixed201_linked
  · exact time201_checked
  · exact ht
  · exact hw
theorem child_geometry201_checked : ReferenceWeightData.CoarseLowerShape.Batch0050.cert402.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0050.cert402.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0050.cert403.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0050.cert403.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights201 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0050.cert402∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch50_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0050.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0050.cert403∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch50_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0050.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0050.cert402.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0050.cert402.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0050.cert402.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry201_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights402_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0050.cert403.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0050.cert403.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry201_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry201_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights403_linked j (List.mem_finRange j))
theorem actual_frozen_frame201 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame201 (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.flow.timeParameter_mem child_geometry201_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights201 hz)
theorem r_profile202_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r202=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds := by rfl
theorem a_profile202_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a202=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a202.bounds := by rfl
theorem r_fixed202_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 7 := by decide +kernel
theorem a_fixed202_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a202.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.a202.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 9 := by decide +kernel
theorem ranks202_linked : ReferenceRankData.CoarseLowerShape.Batch0025.targetR202=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0025.targetA202=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 1 := by decide +kernel
theorem r_input202_linked : ReferenceRankData.CoarseLowerShape.Batch0025.r202.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds.gauge] := by decide +kernel
theorem a_input202_linked : ReferenceRankData.CoarseLowerShape.Batch0025.a202.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.a202.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.a202.bounds.gauge] := by decide +kernel
theorem geometry202_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.a := by decide +kernel
theorem weights404_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0050.cert404.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights405_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0050.cert405.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time202_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 10)=true := by decide +kernel
theorem r_reference202_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 0)=true := by decide +kernel
theorem a_reference202_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 1)=true := by decide +kernel
theorem rank_r_link202_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r202 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link202_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0025.a202.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a202 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints202 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell true ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r202 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile202_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link202_checked
    geometry202_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell false ReferenceProfileData.CoarseLowerShape.Batch0025.a202.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a202 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile202_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link202_checked
    geometry202_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks202_linked.1,←ranks202_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0025.r202.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a202.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0025.ordered202_checked hr ha ho
theorem frozen_frame202 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202 ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds ReferenceProfileData.CoarseLowerShape.Batch0025.a202.bounds
  · rw [←r_profile202_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile202_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry202_linked.2.2.2.2.1
  · exact geometry202_linked.2.2.2.2.2
  · exact r_reference202_checked
  · exact a_reference202_checked
  · exact r_fixed202_linked
  · exact a_fixed202_linked
  · exact time202_checked
  · exact ht
  · exact hw
theorem child_geometry202_checked : ReferenceWeightData.CoarseLowerShape.Batch0050.cert404.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0050.cert404.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0050.cert405.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0050.cert405.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights202 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0050.cert404∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch50_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0050.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0050.cert405∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch50_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0050.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0050.cert404.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0050.cert404.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0050.cert404.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry202_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights404_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0050.cert405.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0050.cert405.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry202_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry202_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights405_linked j (List.mem_finRange j))
theorem actual_frozen_frame202 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame202 (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.flow.timeParameter_mem child_geometry202_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights202 hz)
theorem r_profile203_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r203=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds := by rfl
theorem a_profile203_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a203=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a203.bounds := by rfl
theorem r_fixed203_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 7 := by decide +kernel
theorem a_fixed203_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a203.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.a203.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 9 := by decide +kernel
theorem ranks203_linked : ReferenceRankData.CoarseLowerShape.Batch0025.targetR203=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0025.targetA203=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 1 := by decide +kernel
theorem r_input203_linked : ReferenceRankData.CoarseLowerShape.Batch0025.r203.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds.gauge] := by decide +kernel
theorem a_input203_linked : ReferenceRankData.CoarseLowerShape.Batch0025.a203.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.a203.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.a203.bounds.gauge] := by decide +kernel
theorem geometry203_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.a := by decide +kernel
theorem weights406_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0050.cert406.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights407_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0050.cert407.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time203_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 10)=true := by decide +kernel
theorem r_reference203_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 0)=true := by decide +kernel
theorem a_reference203_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 1)=true := by decide +kernel
theorem rank_r_link203_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r203 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link203_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0025.a203.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a203 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints203 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell true ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r203 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile203_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link203_checked
    geometry203_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell false ReferenceProfileData.CoarseLowerShape.Batch0025.a203.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a203 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile203_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link203_checked
    geometry203_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks203_linked.1,←ranks203_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0025.r203.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a203.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0025.ordered203_checked hr ha ho
theorem frozen_frame203 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203 ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds ReferenceProfileData.CoarseLowerShape.Batch0025.a203.bounds
  · rw [←r_profile203_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile203_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry203_linked.2.2.2.2.1
  · exact geometry203_linked.2.2.2.2.2
  · exact r_reference203_checked
  · exact a_reference203_checked
  · exact r_fixed203_linked
  · exact a_fixed203_linked
  · exact time203_checked
  · exact ht
  · exact hw
theorem child_geometry203_checked : ReferenceWeightData.CoarseLowerShape.Batch0050.cert406.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0050.cert406.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0050.cert407.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0050.cert407.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights203 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0050.cert406∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch50_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0050.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0050.cert407∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch50_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0050.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0050.cert406.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0050.cert406.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0050.cert406.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry203_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights406_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0050.cert407.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0050.cert407.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry203_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry203_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights407_linked j (List.mem_finRange j))
theorem actual_frozen_frame203 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame203 (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.flow.timeParameter_mem child_geometry203_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights203 hz)
theorem r_profile204_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r204=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds := by rfl
theorem a_profile204_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a204=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a204.bounds := by rfl
theorem r_fixed204_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 7 := by decide +kernel
theorem a_fixed204_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a204.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.a204.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 9 := by decide +kernel
theorem ranks204_linked : ReferenceRankData.CoarseLowerShape.Batch0025.targetR204=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0025.targetA204=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 1 := by decide +kernel
theorem r_input204_linked : ReferenceRankData.CoarseLowerShape.Batch0025.r204.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds.gauge] := by decide +kernel
theorem a_input204_linked : ReferenceRankData.CoarseLowerShape.Batch0025.a204.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.a204.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.a204.bounds.gauge] := by decide +kernel
theorem geometry204_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.a := by decide +kernel
theorem weights408_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0051.cert408.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights409_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0051.cert409.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time204_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 10)=true := by decide +kernel
theorem r_reference204_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 0)=true := by decide +kernel
theorem a_reference204_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 1)=true := by decide +kernel
theorem rank_r_link204_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r204 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link204_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0025.a204.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a204 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints204 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell true ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r204 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile204_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link204_checked
    geometry204_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell false ReferenceProfileData.CoarseLowerShape.Batch0025.a204.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a204 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile204_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link204_checked
    geometry204_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks204_linked.1,←ranks204_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0025.r204.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a204.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0025.ordered204_checked hr ha ho
theorem frozen_frame204 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204 ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds ReferenceProfileData.CoarseLowerShape.Batch0025.a204.bounds
  · rw [←r_profile204_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile204_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry204_linked.2.2.2.2.1
  · exact geometry204_linked.2.2.2.2.2
  · exact r_reference204_checked
  · exact a_reference204_checked
  · exact r_fixed204_linked
  · exact a_fixed204_linked
  · exact time204_checked
  · exact ht
  · exact hw
theorem child_geometry204_checked : ReferenceWeightData.CoarseLowerShape.Batch0051.cert408.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0051.cert408.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0051.cert409.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0051.cert409.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights204 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0051.cert408∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch51_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0051.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0051.cert409∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch51_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0051.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0051.cert408.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0051.cert408.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0051.cert408.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry204_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights408_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0051.cert409.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0051.cert409.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry204_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry204_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights409_linked j (List.mem_finRange j))
theorem actual_frozen_frame204 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame204 (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.flow.timeParameter_mem child_geometry204_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights204 hz)
theorem r_profile205_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r205=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds := by rfl
theorem a_profile205_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a205=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a205.bounds := by rfl
theorem r_fixed205_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 7 := by decide +kernel
theorem a_fixed205_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a205.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.a205.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 9 := by decide +kernel
theorem ranks205_linked : ReferenceRankData.CoarseLowerShape.Batch0025.targetR205=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0025.targetA205=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 1 := by decide +kernel
theorem r_input205_linked : ReferenceRankData.CoarseLowerShape.Batch0025.r205.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds.gauge] := by decide +kernel
theorem a_input205_linked : ReferenceRankData.CoarseLowerShape.Batch0025.a205.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.a205.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.a205.bounds.gauge] := by decide +kernel
theorem geometry205_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.a := by decide +kernel
theorem weights410_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0051.cert410.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights411_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0051.cert411.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time205_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 10)=true := by decide +kernel
theorem r_reference205_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 0)=true := by decide +kernel
theorem a_reference205_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 1)=true := by decide +kernel
theorem rank_r_link205_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r205 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link205_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0025.a205.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a205 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints205 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell true ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r205 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile205_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link205_checked
    geometry205_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell false ReferenceProfileData.CoarseLowerShape.Batch0025.a205.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a205 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile205_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link205_checked
    geometry205_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks205_linked.1,←ranks205_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0025.r205.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a205.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0025.ordered205_checked hr ha ho
theorem frozen_frame205 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205 ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds ReferenceProfileData.CoarseLowerShape.Batch0025.a205.bounds
  · rw [←r_profile205_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile205_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry205_linked.2.2.2.2.1
  · exact geometry205_linked.2.2.2.2.2
  · exact r_reference205_checked
  · exact a_reference205_checked
  · exact r_fixed205_linked
  · exact a_fixed205_linked
  · exact time205_checked
  · exact ht
  · exact hw
theorem child_geometry205_checked : ReferenceWeightData.CoarseLowerShape.Batch0051.cert410.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0051.cert410.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0051.cert411.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0051.cert411.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights205 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0051.cert410∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch51_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0051.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0051.cert411∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch51_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0051.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0051.cert410.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0051.cert410.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0051.cert410.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry205_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights410_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0051.cert411.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0051.cert411.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry205_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry205_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights411_linked j (List.mem_finRange j))
theorem actual_frozen_frame205 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame205 (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.flow.timeParameter_mem child_geometry205_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights205 hz)
theorem r_profile206_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r206=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds := by rfl
theorem a_profile206_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a206=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a206.bounds := by rfl
theorem r_fixed206_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 7 := by decide +kernel
theorem a_fixed206_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a206.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.a206.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 9 := by decide +kernel
theorem ranks206_linked : ReferenceRankData.CoarseLowerShape.Batch0025.targetR206=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0025.targetA206=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 1 := by decide +kernel
theorem r_input206_linked : ReferenceRankData.CoarseLowerShape.Batch0025.r206.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds.gauge] := by decide +kernel
theorem a_input206_linked : ReferenceRankData.CoarseLowerShape.Batch0025.a206.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.a206.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.a206.bounds.gauge] := by decide +kernel
theorem geometry206_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.a := by decide +kernel
theorem weights412_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0051.cert412.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights413_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0051.cert413.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time206_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 10)=true := by decide +kernel
theorem r_reference206_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 0)=true := by decide +kernel
theorem a_reference206_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 1)=true := by decide +kernel
theorem rank_r_link206_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r206 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link206_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0025.a206.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a206 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints206 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell true ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r206 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile206_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link206_checked
    geometry206_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell false ReferenceProfileData.CoarseLowerShape.Batch0025.a206.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a206 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile206_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link206_checked
    geometry206_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks206_linked.1,←ranks206_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0025.r206.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a206.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0025.ordered206_checked hr ha ho
theorem frozen_frame206 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206 ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds ReferenceProfileData.CoarseLowerShape.Batch0025.a206.bounds
  · rw [←r_profile206_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile206_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry206_linked.2.2.2.2.1
  · exact geometry206_linked.2.2.2.2.2
  · exact r_reference206_checked
  · exact a_reference206_checked
  · exact r_fixed206_linked
  · exact a_fixed206_linked
  · exact time206_checked
  · exact ht
  · exact hw
theorem child_geometry206_checked : ReferenceWeightData.CoarseLowerShape.Batch0051.cert412.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0051.cert412.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0051.cert413.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0051.cert413.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights206 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0051.cert412∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch51_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0051.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0051.cert413∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch51_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0051.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0051.cert412.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0051.cert412.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0051.cert412.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry206_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights412_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0051.cert413.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0051.cert413.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry206_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry206_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights413_linked j (List.mem_finRange j))
theorem actual_frozen_frame206 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame206 (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.flow.timeParameter_mem child_geometry206_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights206 hz)
theorem r_profile207_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r207=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds := by rfl
theorem a_profile207_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a207=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a207.bounds := by rfl
theorem r_fixed207_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 7 := by decide +kernel
theorem a_fixed207_linked : ReferenceProfileData.CoarseLowerShape.Batch0025.a207.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0025.a207.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 9 := by decide +kernel
theorem ranks207_linked : ReferenceRankData.CoarseLowerShape.Batch0025.targetR207=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0025.targetA207=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 1 := by decide +kernel
theorem r_input207_linked : ReferenceRankData.CoarseLowerShape.Batch0025.r207.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds.gauge] := by decide +kernel
theorem a_input207_linked : ReferenceRankData.CoarseLowerShape.Batch0025.a207.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0025.a207.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0025.a207.bounds.gauge] := by decide +kernel
theorem geometry207_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.a := by decide +kernel
theorem weights414_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0051.cert414.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights415_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0051.cert415.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time207_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 10)=true := by decide +kernel
theorem r_reference207_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 0)=true := by decide +kernel
theorem a_reference207_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 1)=true := by decide +kernel
theorem rank_r_link207_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r207 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link207_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0025.a207.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a207 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints207 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell true ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds ReferenceRankData.CoarseLowerShape.Batch0025.r207 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile207_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link207_checked
    geometry207_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell false ReferenceProfileData.CoarseLowerShape.Batch0025.a207.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a207 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile207_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0025.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0025.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link207_checked
    geometry207_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks207_linked.1,←ranks207_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0025.r207.bounds ReferenceRankData.CoarseLowerShape.Batch0025.a207.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0025.ordered207_checked hr ha ho
theorem frozen_frame207 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207 ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds ReferenceProfileData.CoarseLowerShape.Batch0025.a207.bounds
  · rw [←r_profile207_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile207_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry207_linked.2.2.2.2.1
  · exact geometry207_linked.2.2.2.2.2
  · exact r_reference207_checked
  · exact a_reference207_checked
  · exact r_fixed207_linked
  · exact a_fixed207_linked
  · exact time207_checked
  · exact ht
  · exact hw
theorem child_geometry207_checked : ReferenceWeightData.CoarseLowerShape.Batch0051.cert414.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0051.cert414.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0051.cert415.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0051.cert415.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights207 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0051.cert414∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch51_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0051.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0051.cert415∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch51_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0051.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0051.cert414.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0051.cert414.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0051.cert414.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry207_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights414_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0051.cert415.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0051.cert415.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry207_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry207_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights415_linked j (List.mem_finRange j))
theorem actual_frozen_frame207 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame207 (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.flow.timeParameter_mem child_geometry207_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights207 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell200),(ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell201),(ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell202),(ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell203),(ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell204),(ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell205),(ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell206),(ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0025.cell207)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0025.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0025.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame200 hz
  · exact fun z hz=>actual_frozen_frame201 hz
  · exact fun z hz=>actual_frozen_frame202 hz
  · exact fun z hz=>actual_frozen_frame203 hz
  · exact fun z hz=>actual_frozen_frame204 hz
  · exact fun z hz=>actual_frozen_frame205 hz
  · exact fun z hz=>actual_frozen_frame206 hz
  · exact fun z hz=>actual_frozen_frame207 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints200 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints201 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints202 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints203 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints204 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints205 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints206 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints207 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry200_linked.1,geometry200_linked.2.1,geometry200_linked.2.2.1,geometry200_linked.2.2.2.1⟩
  · exact ⟨geometry201_linked.1,geometry201_linked.2.1,geometry201_linked.2.2.1,geometry201_linked.2.2.2.1⟩
  · exact ⟨geometry202_linked.1,geometry202_linked.2.1,geometry202_linked.2.2.1,geometry202_linked.2.2.2.1⟩
  · exact ⟨geometry203_linked.1,geometry203_linked.2.1,geometry203_linked.2.2.1,geometry203_linked.2.2.2.1⟩
  · exact ⟨geometry204_linked.1,geometry204_linked.2.1,geometry204_linked.2.2.1,geometry204_linked.2.2.2.1⟩
  · exact ⟨geometry205_linked.1,geometry205_linked.2.1,geometry205_linked.2.2.1,geometry205_linked.2.2.2.1⟩
  · exact ⟨geometry206_linked.1,geometry206_linked.2.1,geometry206_linked.2.2.1,geometry206_linked.2.2.2.1⟩
  · exact ⟨geometry207_linked.1,geometry207_linked.2.1,geometry207_linked.2.2.1,geometry207_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.a200.bounds,?_,geometry200_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a200.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile200_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds,?_,geometry200_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert200.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r200.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile200_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.a201.bounds,?_,geometry201_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a201.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile201_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds,?_,geometry201_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert201.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r201.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile201_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.a202.bounds,?_,geometry202_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a202.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile202_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds,?_,geometry202_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert202.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r202.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile202_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.a203.bounds,?_,geometry203_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a203.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile203_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds,?_,geometry203_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert203.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r203.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile203_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.a204.bounds,?_,geometry204_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a204.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile204_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds,?_,geometry204_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert204.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r204.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile204_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.a205.bounds,?_,geometry205_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a205.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile205_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds,?_,geometry205_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert205.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r205.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile205_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.a206.bounds,?_,geometry206_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a206.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile206_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds,?_,geometry206_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert206.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r206.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile206_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.a207.bounds,?_,geometry207_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0025.a207.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile207_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds,?_,geometry207_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0025.cert207.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0025.r207.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile207_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0025.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0025.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0025

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0026
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch52_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0052.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0052.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch53_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0053.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0053.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile208_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r208=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds := by rfl
theorem a_profile208_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a208=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a208.bounds := by rfl
theorem r_fixed208_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 7 := by decide +kernel
theorem a_fixed208_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a208.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.a208.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 9 := by decide +kernel
theorem ranks208_linked : ReferenceRankData.CoarseLowerShape.Batch0026.targetR208=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0026.targetA208=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 1 := by decide +kernel
theorem r_input208_linked : ReferenceRankData.CoarseLowerShape.Batch0026.r208.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds.gauge] := by decide +kernel
theorem a_input208_linked : ReferenceRankData.CoarseLowerShape.Batch0026.a208.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.a208.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.a208.bounds.gauge] := by decide +kernel
theorem geometry208_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.a := by decide +kernel
theorem weights416_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0052.cert416.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights417_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0052.cert417.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time208_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 10)=true := by decide +kernel
theorem r_reference208_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 0)=true := by decide +kernel
theorem a_reference208_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 1)=true := by decide +kernel
theorem rank_r_link208_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r208 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link208_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0026.a208.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a208 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints208 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell true ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r208 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile208_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link208_checked
    geometry208_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell false ReferenceProfileData.CoarseLowerShape.Batch0026.a208.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a208 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile208_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link208_checked
    geometry208_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks208_linked.1,←ranks208_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0026.r208.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a208.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0026.ordered208_checked hr ha ho
theorem frozen_frame208 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208 ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds ReferenceProfileData.CoarseLowerShape.Batch0026.a208.bounds
  · rw [←r_profile208_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile208_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry208_linked.2.2.2.2.1
  · exact geometry208_linked.2.2.2.2.2
  · exact r_reference208_checked
  · exact a_reference208_checked
  · exact r_fixed208_linked
  · exact a_fixed208_linked
  · exact time208_checked
  · exact ht
  · exact hw
theorem child_geometry208_checked : ReferenceWeightData.CoarseLowerShape.Batch0052.cert416.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0052.cert416.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0052.cert417.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0052.cert417.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights208 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0052.cert416∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch52_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0052.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0052.cert417∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch52_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0052.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0052.cert416.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0052.cert416.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0052.cert416.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry208_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights416_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0052.cert417.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0052.cert417.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry208_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry208_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights417_linked j (List.mem_finRange j))
theorem actual_frozen_frame208 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame208 (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.flow.timeParameter_mem child_geometry208_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights208 hz)
theorem r_profile209_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r209=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds := by rfl
theorem a_profile209_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a209=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a209.bounds := by rfl
theorem r_fixed209_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 7 := by decide +kernel
theorem a_fixed209_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a209.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.a209.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 9 := by decide +kernel
theorem ranks209_linked : ReferenceRankData.CoarseLowerShape.Batch0026.targetR209=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0026.targetA209=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 1 := by decide +kernel
theorem r_input209_linked : ReferenceRankData.CoarseLowerShape.Batch0026.r209.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds.gauge] := by decide +kernel
theorem a_input209_linked : ReferenceRankData.CoarseLowerShape.Batch0026.a209.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.a209.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.a209.bounds.gauge] := by decide +kernel
theorem geometry209_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.a := by decide +kernel
theorem weights418_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0052.cert418.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights419_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0052.cert419.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time209_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 10)=true := by decide +kernel
theorem r_reference209_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 0)=true := by decide +kernel
theorem a_reference209_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 1)=true := by decide +kernel
theorem rank_r_link209_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r209 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link209_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0026.a209.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a209 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints209 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell true ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r209 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile209_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link209_checked
    geometry209_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell false ReferenceProfileData.CoarseLowerShape.Batch0026.a209.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a209 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile209_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link209_checked
    geometry209_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks209_linked.1,←ranks209_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0026.r209.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a209.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0026.ordered209_checked hr ha ho
theorem frozen_frame209 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209 ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds ReferenceProfileData.CoarseLowerShape.Batch0026.a209.bounds
  · rw [←r_profile209_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile209_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry209_linked.2.2.2.2.1
  · exact geometry209_linked.2.2.2.2.2
  · exact r_reference209_checked
  · exact a_reference209_checked
  · exact r_fixed209_linked
  · exact a_fixed209_linked
  · exact time209_checked
  · exact ht
  · exact hw
theorem child_geometry209_checked : ReferenceWeightData.CoarseLowerShape.Batch0052.cert418.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0052.cert418.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0052.cert419.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0052.cert419.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights209 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0052.cert418∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch52_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0052.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0052.cert419∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch52_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0052.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0052.cert418.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0052.cert418.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0052.cert418.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry209_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights418_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0052.cert419.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0052.cert419.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry209_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry209_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights419_linked j (List.mem_finRange j))
theorem actual_frozen_frame209 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame209 (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.flow.timeParameter_mem child_geometry209_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights209 hz)
theorem r_profile210_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r210=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds := by rfl
theorem a_profile210_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a210=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a210.bounds := by rfl
theorem r_fixed210_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 7 := by decide +kernel
theorem a_fixed210_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a210.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.a210.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 9 := by decide +kernel
theorem ranks210_linked : ReferenceRankData.CoarseLowerShape.Batch0026.targetR210=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0026.targetA210=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 1 := by decide +kernel
theorem r_input210_linked : ReferenceRankData.CoarseLowerShape.Batch0026.r210.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds.gauge] := by decide +kernel
theorem a_input210_linked : ReferenceRankData.CoarseLowerShape.Batch0026.a210.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.a210.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.a210.bounds.gauge] := by decide +kernel
theorem geometry210_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.a := by decide +kernel
theorem weights420_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0052.cert420.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights421_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0052.cert421.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time210_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 10)=true := by decide +kernel
theorem r_reference210_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 0)=true := by decide +kernel
theorem a_reference210_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 1)=true := by decide +kernel
theorem rank_r_link210_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r210 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link210_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0026.a210.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a210 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints210 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell true ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r210 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile210_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link210_checked
    geometry210_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell false ReferenceProfileData.CoarseLowerShape.Batch0026.a210.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a210 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile210_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link210_checked
    geometry210_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks210_linked.1,←ranks210_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0026.r210.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a210.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0026.ordered210_checked hr ha ho
theorem frozen_frame210 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210 ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds ReferenceProfileData.CoarseLowerShape.Batch0026.a210.bounds
  · rw [←r_profile210_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile210_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry210_linked.2.2.2.2.1
  · exact geometry210_linked.2.2.2.2.2
  · exact r_reference210_checked
  · exact a_reference210_checked
  · exact r_fixed210_linked
  · exact a_fixed210_linked
  · exact time210_checked
  · exact ht
  · exact hw
theorem child_geometry210_checked : ReferenceWeightData.CoarseLowerShape.Batch0052.cert420.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0052.cert420.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0052.cert421.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0052.cert421.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights210 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0052.cert420∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch52_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0052.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0052.cert421∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch52_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0052.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0052.cert420.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0052.cert420.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0052.cert420.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry210_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights420_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0052.cert421.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0052.cert421.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry210_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry210_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights421_linked j (List.mem_finRange j))
theorem actual_frozen_frame210 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame210 (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.flow.timeParameter_mem child_geometry210_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights210 hz)
theorem r_profile211_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r211=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds := by rfl
theorem a_profile211_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a211=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a211.bounds := by rfl
theorem r_fixed211_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 7 := by decide +kernel
theorem a_fixed211_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a211.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.a211.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 9 := by decide +kernel
theorem ranks211_linked : ReferenceRankData.CoarseLowerShape.Batch0026.targetR211=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0026.targetA211=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 1 := by decide +kernel
theorem r_input211_linked : ReferenceRankData.CoarseLowerShape.Batch0026.r211.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds.gauge] := by decide +kernel
theorem a_input211_linked : ReferenceRankData.CoarseLowerShape.Batch0026.a211.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.a211.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.a211.bounds.gauge] := by decide +kernel
theorem geometry211_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.a := by decide +kernel
theorem weights422_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0052.cert422.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights423_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0052.cert423.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time211_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 10)=true := by decide +kernel
theorem r_reference211_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 0)=true := by decide +kernel
theorem a_reference211_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 1)=true := by decide +kernel
theorem rank_r_link211_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r211 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link211_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0026.a211.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a211 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints211 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell true ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r211 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile211_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link211_checked
    geometry211_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell false ReferenceProfileData.CoarseLowerShape.Batch0026.a211.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a211 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile211_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link211_checked
    geometry211_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks211_linked.1,←ranks211_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0026.r211.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a211.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0026.ordered211_checked hr ha ho
theorem frozen_frame211 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211 ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds ReferenceProfileData.CoarseLowerShape.Batch0026.a211.bounds
  · rw [←r_profile211_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile211_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry211_linked.2.2.2.2.1
  · exact geometry211_linked.2.2.2.2.2
  · exact r_reference211_checked
  · exact a_reference211_checked
  · exact r_fixed211_linked
  · exact a_fixed211_linked
  · exact time211_checked
  · exact ht
  · exact hw
theorem child_geometry211_checked : ReferenceWeightData.CoarseLowerShape.Batch0052.cert422.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0052.cert422.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0052.cert423.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0052.cert423.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights211 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0052.cert422∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch52_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0052.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0052.cert423∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch52_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0052.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0052.cert422.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0052.cert422.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0052.cert422.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry211_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights422_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0052.cert423.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0052.cert423.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry211_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry211_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights423_linked j (List.mem_finRange j))
theorem actual_frozen_frame211 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame211 (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.flow.timeParameter_mem child_geometry211_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights211 hz)
theorem r_profile212_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r212=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds := by rfl
theorem a_profile212_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a212=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a212.bounds := by rfl
theorem r_fixed212_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 7 := by decide +kernel
theorem a_fixed212_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a212.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.a212.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 9 := by decide +kernel
theorem ranks212_linked : ReferenceRankData.CoarseLowerShape.Batch0026.targetR212=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0026.targetA212=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 1 := by decide +kernel
theorem r_input212_linked : ReferenceRankData.CoarseLowerShape.Batch0026.r212.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds.gauge] := by decide +kernel
theorem a_input212_linked : ReferenceRankData.CoarseLowerShape.Batch0026.a212.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.a212.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.a212.bounds.gauge] := by decide +kernel
theorem geometry212_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.a := by decide +kernel
theorem weights424_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0053.cert424.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights425_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0053.cert425.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time212_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 10)=true := by decide +kernel
theorem r_reference212_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 0)=true := by decide +kernel
theorem a_reference212_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 1)=true := by decide +kernel
theorem rank_r_link212_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r212 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link212_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0026.a212.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a212 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints212 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell true ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r212 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile212_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link212_checked
    geometry212_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell false ReferenceProfileData.CoarseLowerShape.Batch0026.a212.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a212 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile212_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link212_checked
    geometry212_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks212_linked.1,←ranks212_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0026.r212.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a212.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0026.ordered212_checked hr ha ho
theorem frozen_frame212 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212 ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds ReferenceProfileData.CoarseLowerShape.Batch0026.a212.bounds
  · rw [←r_profile212_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile212_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry212_linked.2.2.2.2.1
  · exact geometry212_linked.2.2.2.2.2
  · exact r_reference212_checked
  · exact a_reference212_checked
  · exact r_fixed212_linked
  · exact a_fixed212_linked
  · exact time212_checked
  · exact ht
  · exact hw
theorem child_geometry212_checked : ReferenceWeightData.CoarseLowerShape.Batch0053.cert424.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0053.cert424.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0053.cert425.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0053.cert425.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights212 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0053.cert424∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch53_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0053.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0053.cert425∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch53_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0053.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0053.cert424.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0053.cert424.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0053.cert424.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry212_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights424_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0053.cert425.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0053.cert425.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry212_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry212_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights425_linked j (List.mem_finRange j))
theorem actual_frozen_frame212 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame212 (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.flow.timeParameter_mem child_geometry212_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights212 hz)
theorem r_profile213_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r213=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds := by rfl
theorem a_profile213_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a213=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a213.bounds := by rfl
theorem r_fixed213_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 7 := by decide +kernel
theorem a_fixed213_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a213.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.a213.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 9 := by decide +kernel
theorem ranks213_linked : ReferenceRankData.CoarseLowerShape.Batch0026.targetR213=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0026.targetA213=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 1 := by decide +kernel
theorem r_input213_linked : ReferenceRankData.CoarseLowerShape.Batch0026.r213.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds.gauge] := by decide +kernel
theorem a_input213_linked : ReferenceRankData.CoarseLowerShape.Batch0026.a213.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.a213.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.a213.bounds.gauge] := by decide +kernel
theorem geometry213_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.a := by decide +kernel
theorem weights426_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0053.cert426.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights427_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0053.cert427.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time213_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 10)=true := by decide +kernel
theorem r_reference213_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 0)=true := by decide +kernel
theorem a_reference213_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 1)=true := by decide +kernel
theorem rank_r_link213_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r213 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link213_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0026.a213.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a213 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints213 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell true ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r213 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile213_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link213_checked
    geometry213_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell false ReferenceProfileData.CoarseLowerShape.Batch0026.a213.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a213 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile213_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link213_checked
    geometry213_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks213_linked.1,←ranks213_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0026.r213.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a213.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0026.ordered213_checked hr ha ho
theorem frozen_frame213 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213 ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds ReferenceProfileData.CoarseLowerShape.Batch0026.a213.bounds
  · rw [←r_profile213_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile213_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry213_linked.2.2.2.2.1
  · exact geometry213_linked.2.2.2.2.2
  · exact r_reference213_checked
  · exact a_reference213_checked
  · exact r_fixed213_linked
  · exact a_fixed213_linked
  · exact time213_checked
  · exact ht
  · exact hw
theorem child_geometry213_checked : ReferenceWeightData.CoarseLowerShape.Batch0053.cert426.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0053.cert426.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0053.cert427.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0053.cert427.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights213 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0053.cert426∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch53_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0053.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0053.cert427∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch53_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0053.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0053.cert426.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0053.cert426.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0053.cert426.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry213_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights426_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0053.cert427.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0053.cert427.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry213_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry213_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights427_linked j (List.mem_finRange j))
theorem actual_frozen_frame213 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame213 (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.flow.timeParameter_mem child_geometry213_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights213 hz)
theorem r_profile214_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r214=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds := by rfl
theorem a_profile214_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a214=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a214.bounds := by rfl
theorem r_fixed214_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 7 := by decide +kernel
theorem a_fixed214_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a214.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.a214.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 9 := by decide +kernel
theorem ranks214_linked : ReferenceRankData.CoarseLowerShape.Batch0026.targetR214=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0026.targetA214=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 1 := by decide +kernel
theorem r_input214_linked : ReferenceRankData.CoarseLowerShape.Batch0026.r214.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds.gauge] := by decide +kernel
theorem a_input214_linked : ReferenceRankData.CoarseLowerShape.Batch0026.a214.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.a214.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.a214.bounds.gauge] := by decide +kernel
theorem geometry214_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.a := by decide +kernel
theorem weights428_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0053.cert428.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights429_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0053.cert429.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time214_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 10)=true := by decide +kernel
theorem r_reference214_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 0)=true := by decide +kernel
theorem a_reference214_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 1)=true := by decide +kernel
theorem rank_r_link214_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r214 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link214_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0026.a214.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a214 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints214 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell true ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r214 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile214_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link214_checked
    geometry214_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell false ReferenceProfileData.CoarseLowerShape.Batch0026.a214.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a214 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile214_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link214_checked
    geometry214_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks214_linked.1,←ranks214_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0026.r214.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a214.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0026.ordered214_checked hr ha ho
theorem frozen_frame214 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214 ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds ReferenceProfileData.CoarseLowerShape.Batch0026.a214.bounds
  · rw [←r_profile214_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile214_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry214_linked.2.2.2.2.1
  · exact geometry214_linked.2.2.2.2.2
  · exact r_reference214_checked
  · exact a_reference214_checked
  · exact r_fixed214_linked
  · exact a_fixed214_linked
  · exact time214_checked
  · exact ht
  · exact hw
theorem child_geometry214_checked : ReferenceWeightData.CoarseLowerShape.Batch0053.cert428.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0053.cert428.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0053.cert429.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0053.cert429.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights214 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0053.cert428∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch53_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0053.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0053.cert429∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch53_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0053.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0053.cert428.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0053.cert428.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0053.cert428.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry214_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights428_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0053.cert429.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0053.cert429.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry214_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry214_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights429_linked j (List.mem_finRange j))
theorem actual_frozen_frame214 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame214 (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.flow.timeParameter_mem child_geometry214_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights214 hz)
theorem r_profile215_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r215=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds := by rfl
theorem a_profile215_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a215=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a215.bounds := by rfl
theorem r_fixed215_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 7 := by decide +kernel
theorem a_fixed215_linked : ReferenceProfileData.CoarseLowerShape.Batch0026.a215.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0026.a215.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 9 := by decide +kernel
theorem ranks215_linked : ReferenceRankData.CoarseLowerShape.Batch0026.targetR215=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0026.targetA215=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 1 := by decide +kernel
theorem r_input215_linked : ReferenceRankData.CoarseLowerShape.Batch0026.r215.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds.gauge] := by decide +kernel
theorem a_input215_linked : ReferenceRankData.CoarseLowerShape.Batch0026.a215.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0026.a215.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0026.a215.bounds.gauge] := by decide +kernel
theorem geometry215_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.a := by decide +kernel
theorem weights430_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0053.cert430.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights431_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0053.cert431.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time215_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 10)=true := by decide +kernel
theorem r_reference215_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 0)=true := by decide +kernel
theorem a_reference215_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 1)=true := by decide +kernel
theorem rank_r_link215_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r215 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link215_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0026.a215.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a215 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints215 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell true ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds ReferenceRankData.CoarseLowerShape.Batch0026.r215 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile215_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link215_checked
    geometry215_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell false ReferenceProfileData.CoarseLowerShape.Batch0026.a215.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a215 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile215_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0026.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0026.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link215_checked
    geometry215_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks215_linked.1,←ranks215_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0026.r215.bounds ReferenceRankData.CoarseLowerShape.Batch0026.a215.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0026.ordered215_checked hr ha ho
theorem frozen_frame215 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215 ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds ReferenceProfileData.CoarseLowerShape.Batch0026.a215.bounds
  · rw [←r_profile215_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile215_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry215_linked.2.2.2.2.1
  · exact geometry215_linked.2.2.2.2.2
  · exact r_reference215_checked
  · exact a_reference215_checked
  · exact r_fixed215_linked
  · exact a_fixed215_linked
  · exact time215_checked
  · exact ht
  · exact hw
theorem child_geometry215_checked : ReferenceWeightData.CoarseLowerShape.Batch0053.cert430.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0053.cert430.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0053.cert431.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0053.cert431.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights215 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0053.cert430∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch53_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0053.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0053.cert431∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch53_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0053.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0053.cert430.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0053.cert430.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0053.cert430.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry215_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights430_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0053.cert431.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0053.cert431.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry215_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry215_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights431_linked j (List.mem_finRange j))
theorem actual_frozen_frame215 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame215 (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.flow.timeParameter_mem child_geometry215_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights215 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell208),(ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell209),(ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell210),(ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell211),(ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell212),(ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell213),(ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell214),(ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0026.cell215)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0026.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0026.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame208 hz
  · exact fun z hz=>actual_frozen_frame209 hz
  · exact fun z hz=>actual_frozen_frame210 hz
  · exact fun z hz=>actual_frozen_frame211 hz
  · exact fun z hz=>actual_frozen_frame212 hz
  · exact fun z hz=>actual_frozen_frame213 hz
  · exact fun z hz=>actual_frozen_frame214 hz
  · exact fun z hz=>actual_frozen_frame215 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints208 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints209 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints210 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints211 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints212 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints213 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints214 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints215 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry208_linked.1,geometry208_linked.2.1,geometry208_linked.2.2.1,geometry208_linked.2.2.2.1⟩
  · exact ⟨geometry209_linked.1,geometry209_linked.2.1,geometry209_linked.2.2.1,geometry209_linked.2.2.2.1⟩
  · exact ⟨geometry210_linked.1,geometry210_linked.2.1,geometry210_linked.2.2.1,geometry210_linked.2.2.2.1⟩
  · exact ⟨geometry211_linked.1,geometry211_linked.2.1,geometry211_linked.2.2.1,geometry211_linked.2.2.2.1⟩
  · exact ⟨geometry212_linked.1,geometry212_linked.2.1,geometry212_linked.2.2.1,geometry212_linked.2.2.2.1⟩
  · exact ⟨geometry213_linked.1,geometry213_linked.2.1,geometry213_linked.2.2.1,geometry213_linked.2.2.2.1⟩
  · exact ⟨geometry214_linked.1,geometry214_linked.2.1,geometry214_linked.2.2.1,geometry214_linked.2.2.2.1⟩
  · exact ⟨geometry215_linked.1,geometry215_linked.2.1,geometry215_linked.2.2.1,geometry215_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.a208.bounds,?_,geometry208_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a208.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile208_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds,?_,geometry208_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert208.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r208.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile208_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.a209.bounds,?_,geometry209_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a209.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile209_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds,?_,geometry209_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert209.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r209.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile209_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.a210.bounds,?_,geometry210_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a210.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile210_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds,?_,geometry210_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert210.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r210.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile210_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.a211.bounds,?_,geometry211_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a211.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile211_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds,?_,geometry211_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert211.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r211.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile211_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.a212.bounds,?_,geometry212_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a212.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile212_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds,?_,geometry212_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert212.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r212.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile212_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.a213.bounds,?_,geometry213_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a213.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile213_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds,?_,geometry213_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert213.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r213.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile213_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.a214.bounds,?_,geometry214_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a214.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile214_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds,?_,geometry214_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert214.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r214.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile214_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.a215.bounds,?_,geometry215_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0026.a215.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile215_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds,?_,geometry215_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0026.cert215.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0026.r215.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile215_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0026.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0026.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0026

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0027
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch54_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0054.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0054.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch55_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0055.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0055.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile216_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r216=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds := by rfl
theorem a_profile216_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a216=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a216.bounds := by rfl
theorem r_fixed216_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 7 := by decide +kernel
theorem a_fixed216_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a216.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.a216.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 9 := by decide +kernel
theorem ranks216_linked : ReferenceRankData.CoarseLowerShape.Batch0027.targetR216=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0027.targetA216=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 1 := by decide +kernel
theorem r_input216_linked : ReferenceRankData.CoarseLowerShape.Batch0027.r216.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds.gauge] := by decide +kernel
theorem a_input216_linked : ReferenceRankData.CoarseLowerShape.Batch0027.a216.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.a216.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.a216.bounds.gauge] := by decide +kernel
theorem geometry216_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.a := by decide +kernel
theorem weights432_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0054.cert432.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights433_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0054.cert433.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time216_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 10)=true := by decide +kernel
theorem r_reference216_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 0)=true := by decide +kernel
theorem a_reference216_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 1)=true := by decide +kernel
theorem rank_r_link216_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r216 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link216_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0027.a216.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a216 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints216 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell true ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r216 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile216_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link216_checked
    geometry216_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell false ReferenceProfileData.CoarseLowerShape.Batch0027.a216.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a216 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile216_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link216_checked
    geometry216_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks216_linked.1,←ranks216_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0027.r216.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a216.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0027.ordered216_checked hr ha ho
theorem frozen_frame216 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216 ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds ReferenceProfileData.CoarseLowerShape.Batch0027.a216.bounds
  · rw [←r_profile216_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile216_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry216_linked.2.2.2.2.1
  · exact geometry216_linked.2.2.2.2.2
  · exact r_reference216_checked
  · exact a_reference216_checked
  · exact r_fixed216_linked
  · exact a_fixed216_linked
  · exact time216_checked
  · exact ht
  · exact hw
theorem child_geometry216_checked : ReferenceWeightData.CoarseLowerShape.Batch0054.cert432.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0054.cert432.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0054.cert433.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0054.cert433.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights216 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0054.cert432∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch54_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0054.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0054.cert433∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch54_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0054.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0054.cert432.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0054.cert432.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0054.cert432.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry216_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights432_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0054.cert433.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0054.cert433.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry216_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry216_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights433_linked j (List.mem_finRange j))
theorem actual_frozen_frame216 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame216 (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.flow.timeParameter_mem child_geometry216_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights216 hz)
theorem r_profile217_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r217=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds := by rfl
theorem a_profile217_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a217=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a217.bounds := by rfl
theorem r_fixed217_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 7 := by decide +kernel
theorem a_fixed217_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a217.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.a217.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 9 := by decide +kernel
theorem ranks217_linked : ReferenceRankData.CoarseLowerShape.Batch0027.targetR217=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0027.targetA217=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 1 := by decide +kernel
theorem r_input217_linked : ReferenceRankData.CoarseLowerShape.Batch0027.r217.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds.gauge] := by decide +kernel
theorem a_input217_linked : ReferenceRankData.CoarseLowerShape.Batch0027.a217.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.a217.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.a217.bounds.gauge] := by decide +kernel
theorem geometry217_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.a := by decide +kernel
theorem weights434_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0054.cert434.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights435_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0054.cert435.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time217_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 10)=true := by decide +kernel
theorem r_reference217_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 0)=true := by decide +kernel
theorem a_reference217_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 1)=true := by decide +kernel
theorem rank_r_link217_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r217 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link217_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0027.a217.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a217 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints217 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell true ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r217 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile217_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link217_checked
    geometry217_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell false ReferenceProfileData.CoarseLowerShape.Batch0027.a217.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a217 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile217_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link217_checked
    geometry217_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks217_linked.1,←ranks217_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0027.r217.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a217.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0027.ordered217_checked hr ha ho
theorem frozen_frame217 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217 ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds ReferenceProfileData.CoarseLowerShape.Batch0027.a217.bounds
  · rw [←r_profile217_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile217_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry217_linked.2.2.2.2.1
  · exact geometry217_linked.2.2.2.2.2
  · exact r_reference217_checked
  · exact a_reference217_checked
  · exact r_fixed217_linked
  · exact a_fixed217_linked
  · exact time217_checked
  · exact ht
  · exact hw
theorem child_geometry217_checked : ReferenceWeightData.CoarseLowerShape.Batch0054.cert434.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0054.cert434.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0054.cert435.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0054.cert435.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights217 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0054.cert434∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch54_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0054.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0054.cert435∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch54_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0054.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0054.cert434.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0054.cert434.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0054.cert434.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry217_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights434_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0054.cert435.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0054.cert435.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry217_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry217_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights435_linked j (List.mem_finRange j))
theorem actual_frozen_frame217 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame217 (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.flow.timeParameter_mem child_geometry217_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights217 hz)
theorem r_profile218_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r218=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds := by rfl
theorem a_profile218_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a218=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a218.bounds := by rfl
theorem r_fixed218_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 7 := by decide +kernel
theorem a_fixed218_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a218.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.a218.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 9 := by decide +kernel
theorem ranks218_linked : ReferenceRankData.CoarseLowerShape.Batch0027.targetR218=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0027.targetA218=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 1 := by decide +kernel
theorem r_input218_linked : ReferenceRankData.CoarseLowerShape.Batch0027.r218.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds.gauge] := by decide +kernel
theorem a_input218_linked : ReferenceRankData.CoarseLowerShape.Batch0027.a218.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.a218.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.a218.bounds.gauge] := by decide +kernel
theorem geometry218_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.a := by decide +kernel
theorem weights436_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0054.cert436.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights437_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0054.cert437.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time218_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 10)=true := by decide +kernel
theorem r_reference218_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 0)=true := by decide +kernel
theorem a_reference218_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 1)=true := by decide +kernel
theorem rank_r_link218_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r218 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link218_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0027.a218.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a218 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints218 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell true ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r218 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile218_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link218_checked
    geometry218_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell false ReferenceProfileData.CoarseLowerShape.Batch0027.a218.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a218 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile218_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link218_checked
    geometry218_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks218_linked.1,←ranks218_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0027.r218.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a218.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0027.ordered218_checked hr ha ho
theorem frozen_frame218 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218 ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds ReferenceProfileData.CoarseLowerShape.Batch0027.a218.bounds
  · rw [←r_profile218_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile218_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry218_linked.2.2.2.2.1
  · exact geometry218_linked.2.2.2.2.2
  · exact r_reference218_checked
  · exact a_reference218_checked
  · exact r_fixed218_linked
  · exact a_fixed218_linked
  · exact time218_checked
  · exact ht
  · exact hw
theorem child_geometry218_checked : ReferenceWeightData.CoarseLowerShape.Batch0054.cert436.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0054.cert436.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0054.cert437.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0054.cert437.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights218 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0054.cert436∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch54_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0054.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0054.cert437∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch54_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0054.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0054.cert436.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0054.cert436.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0054.cert436.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry218_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights436_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0054.cert437.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0054.cert437.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry218_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry218_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights437_linked j (List.mem_finRange j))
theorem actual_frozen_frame218 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame218 (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.flow.timeParameter_mem child_geometry218_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights218 hz)
theorem r_profile219_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r219=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds := by rfl
theorem a_profile219_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a219=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a219.bounds := by rfl
theorem r_fixed219_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 7 := by decide +kernel
theorem a_fixed219_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a219.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.a219.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 9 := by decide +kernel
theorem ranks219_linked : ReferenceRankData.CoarseLowerShape.Batch0027.targetR219=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0027.targetA219=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 1 := by decide +kernel
theorem r_input219_linked : ReferenceRankData.CoarseLowerShape.Batch0027.r219.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds.gauge] := by decide +kernel
theorem a_input219_linked : ReferenceRankData.CoarseLowerShape.Batch0027.a219.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.a219.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.a219.bounds.gauge] := by decide +kernel
theorem geometry219_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.a := by decide +kernel
theorem weights438_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0054.cert438.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights439_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0054.cert439.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time219_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 10)=true := by decide +kernel
theorem r_reference219_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 0)=true := by decide +kernel
theorem a_reference219_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 1)=true := by decide +kernel
theorem rank_r_link219_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r219 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link219_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0027.a219.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a219 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints219 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell true ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r219 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile219_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link219_checked
    geometry219_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell false ReferenceProfileData.CoarseLowerShape.Batch0027.a219.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a219 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile219_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link219_checked
    geometry219_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks219_linked.1,←ranks219_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0027.r219.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a219.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0027.ordered219_checked hr ha ho
theorem frozen_frame219 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219 ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds ReferenceProfileData.CoarseLowerShape.Batch0027.a219.bounds
  · rw [←r_profile219_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile219_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry219_linked.2.2.2.2.1
  · exact geometry219_linked.2.2.2.2.2
  · exact r_reference219_checked
  · exact a_reference219_checked
  · exact r_fixed219_linked
  · exact a_fixed219_linked
  · exact time219_checked
  · exact ht
  · exact hw
theorem child_geometry219_checked : ReferenceWeightData.CoarseLowerShape.Batch0054.cert438.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0054.cert438.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0054.cert439.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0054.cert439.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights219 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0054.cert438∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch54_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0054.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0054.cert439∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch54_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0054.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0054.cert438.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0054.cert438.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0054.cert438.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry219_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights438_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0054.cert439.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0054.cert439.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry219_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry219_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights439_linked j (List.mem_finRange j))
theorem actual_frozen_frame219 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame219 (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.flow.timeParameter_mem child_geometry219_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights219 hz)
theorem r_profile220_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r220=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds := by rfl
theorem a_profile220_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a220=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a220.bounds := by rfl
theorem r_fixed220_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 7 := by decide +kernel
theorem a_fixed220_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a220.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.a220.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 9 := by decide +kernel
theorem ranks220_linked : ReferenceRankData.CoarseLowerShape.Batch0027.targetR220=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0027.targetA220=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 1 := by decide +kernel
theorem r_input220_linked : ReferenceRankData.CoarseLowerShape.Batch0027.r220.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds.gauge] := by decide +kernel
theorem a_input220_linked : ReferenceRankData.CoarseLowerShape.Batch0027.a220.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.a220.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.a220.bounds.gauge] := by decide +kernel
theorem geometry220_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.a := by decide +kernel
theorem weights440_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0055.cert440.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights441_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0055.cert441.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time220_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 10)=true := by decide +kernel
theorem r_reference220_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 0)=true := by decide +kernel
theorem a_reference220_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 1)=true := by decide +kernel
theorem rank_r_link220_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r220 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link220_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0027.a220.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a220 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints220 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell true ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r220 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile220_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link220_checked
    geometry220_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell false ReferenceProfileData.CoarseLowerShape.Batch0027.a220.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a220 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile220_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link220_checked
    geometry220_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks220_linked.1,←ranks220_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0027.r220.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a220.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0027.ordered220_checked hr ha ho
theorem frozen_frame220 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220 ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds ReferenceProfileData.CoarseLowerShape.Batch0027.a220.bounds
  · rw [←r_profile220_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile220_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry220_linked.2.2.2.2.1
  · exact geometry220_linked.2.2.2.2.2
  · exact r_reference220_checked
  · exact a_reference220_checked
  · exact r_fixed220_linked
  · exact a_fixed220_linked
  · exact time220_checked
  · exact ht
  · exact hw
theorem child_geometry220_checked : ReferenceWeightData.CoarseLowerShape.Batch0055.cert440.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0055.cert440.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0055.cert441.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0055.cert441.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights220 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0055.cert440∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch55_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0055.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0055.cert441∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch55_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0055.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0055.cert440.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0055.cert440.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0055.cert440.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry220_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights440_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0055.cert441.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0055.cert441.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry220_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry220_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights441_linked j (List.mem_finRange j))
theorem actual_frozen_frame220 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame220 (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.flow.timeParameter_mem child_geometry220_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights220 hz)
theorem r_profile221_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r221=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds := by rfl
theorem a_profile221_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a221=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a221.bounds := by rfl
theorem r_fixed221_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 7 := by decide +kernel
theorem a_fixed221_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a221.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.a221.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 9 := by decide +kernel
theorem ranks221_linked : ReferenceRankData.CoarseLowerShape.Batch0027.targetR221=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0027.targetA221=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 1 := by decide +kernel
theorem r_input221_linked : ReferenceRankData.CoarseLowerShape.Batch0027.r221.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds.gauge] := by decide +kernel
theorem a_input221_linked : ReferenceRankData.CoarseLowerShape.Batch0027.a221.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.a221.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.a221.bounds.gauge] := by decide +kernel
theorem geometry221_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.a := by decide +kernel
theorem weights442_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0055.cert442.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights443_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0055.cert443.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time221_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 10)=true := by decide +kernel
theorem r_reference221_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 0)=true := by decide +kernel
theorem a_reference221_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 1)=true := by decide +kernel
theorem rank_r_link221_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r221 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link221_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0027.a221.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a221 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints221 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell true ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r221 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile221_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link221_checked
    geometry221_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell false ReferenceProfileData.CoarseLowerShape.Batch0027.a221.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a221 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile221_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link221_checked
    geometry221_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks221_linked.1,←ranks221_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0027.r221.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a221.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0027.ordered221_checked hr ha ho
theorem frozen_frame221 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221 ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds ReferenceProfileData.CoarseLowerShape.Batch0027.a221.bounds
  · rw [←r_profile221_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile221_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry221_linked.2.2.2.2.1
  · exact geometry221_linked.2.2.2.2.2
  · exact r_reference221_checked
  · exact a_reference221_checked
  · exact r_fixed221_linked
  · exact a_fixed221_linked
  · exact time221_checked
  · exact ht
  · exact hw
theorem child_geometry221_checked : ReferenceWeightData.CoarseLowerShape.Batch0055.cert442.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0055.cert442.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0055.cert443.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0055.cert443.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights221 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0055.cert442∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch55_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0055.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0055.cert443∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch55_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0055.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0055.cert442.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0055.cert442.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0055.cert442.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry221_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights442_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0055.cert443.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0055.cert443.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry221_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry221_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights443_linked j (List.mem_finRange j))
theorem actual_frozen_frame221 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame221 (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.flow.timeParameter_mem child_geometry221_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights221 hz)
theorem r_profile222_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r222=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds := by rfl
theorem a_profile222_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a222=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a222.bounds := by rfl
theorem r_fixed222_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 7 := by decide +kernel
theorem a_fixed222_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a222.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.a222.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 9 := by decide +kernel
theorem ranks222_linked : ReferenceRankData.CoarseLowerShape.Batch0027.targetR222=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0027.targetA222=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 1 := by decide +kernel
theorem r_input222_linked : ReferenceRankData.CoarseLowerShape.Batch0027.r222.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds.gauge] := by decide +kernel
theorem a_input222_linked : ReferenceRankData.CoarseLowerShape.Batch0027.a222.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.a222.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.a222.bounds.gauge] := by decide +kernel
theorem geometry222_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.a := by decide +kernel
theorem weights444_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0055.cert444.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights445_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0055.cert445.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time222_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 10)=true := by decide +kernel
theorem r_reference222_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 0)=true := by decide +kernel
theorem a_reference222_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 1)=true := by decide +kernel
theorem rank_r_link222_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r222 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link222_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0027.a222.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a222 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints222 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell true ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r222 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile222_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link222_checked
    geometry222_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell false ReferenceProfileData.CoarseLowerShape.Batch0027.a222.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a222 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile222_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link222_checked
    geometry222_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks222_linked.1,←ranks222_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0027.r222.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a222.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0027.ordered222_checked hr ha ho
theorem frozen_frame222 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222 ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds ReferenceProfileData.CoarseLowerShape.Batch0027.a222.bounds
  · rw [←r_profile222_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile222_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry222_linked.2.2.2.2.1
  · exact geometry222_linked.2.2.2.2.2
  · exact r_reference222_checked
  · exact a_reference222_checked
  · exact r_fixed222_linked
  · exact a_fixed222_linked
  · exact time222_checked
  · exact ht
  · exact hw
theorem child_geometry222_checked : ReferenceWeightData.CoarseLowerShape.Batch0055.cert444.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0055.cert444.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0055.cert445.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0055.cert445.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights222 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0055.cert444∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch55_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0055.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0055.cert445∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch55_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0055.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0055.cert444.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0055.cert444.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0055.cert444.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry222_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights444_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0055.cert445.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0055.cert445.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry222_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry222_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights445_linked j (List.mem_finRange j))
theorem actual_frozen_frame222 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame222 (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.flow.timeParameter_mem child_geometry222_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights222 hz)
theorem r_profile223_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r223=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds := by rfl
theorem a_profile223_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a223=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a223.bounds := by rfl
theorem r_fixed223_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 7 := by decide +kernel
theorem a_fixed223_linked : ReferenceProfileData.CoarseLowerShape.Batch0027.a223.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0027.a223.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 9 := by decide +kernel
theorem ranks223_linked : ReferenceRankData.CoarseLowerShape.Batch0027.targetR223=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0027.targetA223=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 1 := by decide +kernel
theorem r_input223_linked : ReferenceRankData.CoarseLowerShape.Batch0027.r223.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds.gauge] := by decide +kernel
theorem a_input223_linked : ReferenceRankData.CoarseLowerShape.Batch0027.a223.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0027.a223.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0027.a223.bounds.gauge] := by decide +kernel
theorem geometry223_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.a := by decide +kernel
theorem weights446_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0055.cert446.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights447_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0055.cert447.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time223_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 10)=true := by decide +kernel
theorem r_reference223_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 0)=true := by decide +kernel
theorem a_reference223_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 1)=true := by decide +kernel
theorem rank_r_link223_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r223 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link223_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0027.a223.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a223 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints223 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell true ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds ReferenceRankData.CoarseLowerShape.Batch0027.r223 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile223_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link223_checked
    geometry223_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell false ReferenceProfileData.CoarseLowerShape.Batch0027.a223.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a223 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile223_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0027.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0027.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link223_checked
    geometry223_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks223_linked.1,←ranks223_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0027.r223.bounds ReferenceRankData.CoarseLowerShape.Batch0027.a223.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0027.ordered223_checked hr ha ho
theorem frozen_frame223 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223 ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds ReferenceProfileData.CoarseLowerShape.Batch0027.a223.bounds
  · rw [←r_profile223_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile223_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry223_linked.2.2.2.2.1
  · exact geometry223_linked.2.2.2.2.2
  · exact r_reference223_checked
  · exact a_reference223_checked
  · exact r_fixed223_linked
  · exact a_fixed223_linked
  · exact time223_checked
  · exact ht
  · exact hw
theorem child_geometry223_checked : ReferenceWeightData.CoarseLowerShape.Batch0055.cert446.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0055.cert446.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0055.cert447.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0055.cert447.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights223 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0055.cert446∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch55_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0055.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0055.cert447∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch55_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0055.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0055.cert446.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0055.cert446.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0055.cert446.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry223_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights446_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0055.cert447.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0055.cert447.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry223_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry223_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights447_linked j (List.mem_finRange j))
theorem actual_frozen_frame223 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame223 (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.flow.timeParameter_mem child_geometry223_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights223 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell216),(ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell217),(ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell218),(ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell219),(ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell220),(ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell221),(ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell222),(ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0027.cell223)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0027.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0027.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame216 hz
  · exact fun z hz=>actual_frozen_frame217 hz
  · exact fun z hz=>actual_frozen_frame218 hz
  · exact fun z hz=>actual_frozen_frame219 hz
  · exact fun z hz=>actual_frozen_frame220 hz
  · exact fun z hz=>actual_frozen_frame221 hz
  · exact fun z hz=>actual_frozen_frame222 hz
  · exact fun z hz=>actual_frozen_frame223 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints216 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints217 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints218 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints219 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints220 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints221 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints222 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints223 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry216_linked.1,geometry216_linked.2.1,geometry216_linked.2.2.1,geometry216_linked.2.2.2.1⟩
  · exact ⟨geometry217_linked.1,geometry217_linked.2.1,geometry217_linked.2.2.1,geometry217_linked.2.2.2.1⟩
  · exact ⟨geometry218_linked.1,geometry218_linked.2.1,geometry218_linked.2.2.1,geometry218_linked.2.2.2.1⟩
  · exact ⟨geometry219_linked.1,geometry219_linked.2.1,geometry219_linked.2.2.1,geometry219_linked.2.2.2.1⟩
  · exact ⟨geometry220_linked.1,geometry220_linked.2.1,geometry220_linked.2.2.1,geometry220_linked.2.2.2.1⟩
  · exact ⟨geometry221_linked.1,geometry221_linked.2.1,geometry221_linked.2.2.1,geometry221_linked.2.2.2.1⟩
  · exact ⟨geometry222_linked.1,geometry222_linked.2.1,geometry222_linked.2.2.1,geometry222_linked.2.2.2.1⟩
  · exact ⟨geometry223_linked.1,geometry223_linked.2.1,geometry223_linked.2.2.1,geometry223_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.a216.bounds,?_,geometry216_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a216.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile216_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds,?_,geometry216_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert216.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r216.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile216_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.a217.bounds,?_,geometry217_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a217.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile217_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds,?_,geometry217_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert217.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r217.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile217_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.a218.bounds,?_,geometry218_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a218.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile218_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds,?_,geometry218_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert218.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r218.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile218_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.a219.bounds,?_,geometry219_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a219.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile219_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds,?_,geometry219_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert219.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r219.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile219_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.a220.bounds,?_,geometry220_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a220.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile220_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds,?_,geometry220_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert220.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r220.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile220_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.a221.bounds,?_,geometry221_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a221.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile221_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds,?_,geometry221_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert221.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r221.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile221_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.a222.bounds,?_,geometry222_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a222.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile222_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds,?_,geometry222_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert222.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r222.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile222_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.a223.bounds,?_,geometry223_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0027.a223.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile223_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds,?_,geometry223_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0027.cert223.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0027.r223.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile223_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0027.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0027.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0027
