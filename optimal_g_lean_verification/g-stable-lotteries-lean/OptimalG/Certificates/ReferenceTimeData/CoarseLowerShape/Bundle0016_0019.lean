import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0013_0016
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0013_0016
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0033_0036
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0014_0017
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0015_0018
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Bundle0012_0015
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0017_0020
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0017_0020
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0037_0040
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0018_0021
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0019_0022

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0016
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch32_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0032.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0032.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch33_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0033.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0033.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile128_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r128=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds := by rfl
theorem a_profile128_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a128=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a128.bounds := by rfl
theorem r_fixed128_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 7 := by decide +kernel
theorem a_fixed128_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a128.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.a128.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 9 := by decide +kernel
theorem ranks128_linked : ReferenceRankData.CoarseLowerShape.Batch0016.targetR128=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0016.targetA128=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 1 := by decide +kernel
theorem r_input128_linked : ReferenceRankData.CoarseLowerShape.Batch0016.r128.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds.gauge] := by decide +kernel
theorem a_input128_linked : ReferenceRankData.CoarseLowerShape.Batch0016.a128.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.a128.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.a128.bounds.gauge] := by decide +kernel
theorem geometry128_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.a := by decide +kernel
theorem weights256_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0032.cert256.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights257_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0032.cert257.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time128_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 10)=true := by decide +kernel
theorem r_reference128_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 0)=true := by decide +kernel
theorem a_reference128_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 1)=true := by decide +kernel
theorem rank_r_link128_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r128 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link128_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0016.a128.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a128 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints128 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell true ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r128 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile128_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link128_checked
    geometry128_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell false ReferenceProfileData.CoarseLowerShape.Batch0016.a128.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a128 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile128_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link128_checked
    geometry128_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks128_linked.1,←ranks128_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0016.r128.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a128.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0016.ordered128_checked hr ha ho
theorem frozen_frame128 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128 ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds ReferenceProfileData.CoarseLowerShape.Batch0016.a128.bounds
  · rw [←r_profile128_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile128_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry128_linked.2.2.2.2.1
  · exact geometry128_linked.2.2.2.2.2
  · exact r_reference128_checked
  · exact a_reference128_checked
  · exact r_fixed128_linked
  · exact a_fixed128_linked
  · exact time128_checked
  · exact ht
  · exact hw
theorem child_geometry128_checked : ReferenceWeightData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights128 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0032.cert256∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch32_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0032.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0032.cert257∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch32_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0032.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0032.cert256.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry128_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights256_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0032.cert257.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry128_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry128_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights257_linked j (List.mem_finRange j))
theorem actual_frozen_frame128 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame128 (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.flow.timeParameter_mem child_geometry128_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights128 hz)
theorem r_profile129_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r129=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds := by rfl
theorem a_profile129_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a129=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a129.bounds := by rfl
theorem r_fixed129_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 7 := by decide +kernel
theorem a_fixed129_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a129.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.a129.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 9 := by decide +kernel
theorem ranks129_linked : ReferenceRankData.CoarseLowerShape.Batch0016.targetR129=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0016.targetA129=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 1 := by decide +kernel
theorem r_input129_linked : ReferenceRankData.CoarseLowerShape.Batch0016.r129.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds.gauge] := by decide +kernel
theorem a_input129_linked : ReferenceRankData.CoarseLowerShape.Batch0016.a129.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.a129.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.a129.bounds.gauge] := by decide +kernel
theorem geometry129_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.a := by decide +kernel
theorem weights258_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0032.cert258.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights259_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0032.cert259.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time129_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 10)=true := by decide +kernel
theorem r_reference129_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 0)=true := by decide +kernel
theorem a_reference129_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 1)=true := by decide +kernel
theorem rank_r_link129_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r129 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link129_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0016.a129.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a129 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints129 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell true ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r129 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile129_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link129_checked
    geometry129_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell false ReferenceProfileData.CoarseLowerShape.Batch0016.a129.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a129 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile129_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link129_checked
    geometry129_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks129_linked.1,←ranks129_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0016.r129.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a129.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0016.ordered129_checked hr ha ho
theorem frozen_frame129 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129 ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds ReferenceProfileData.CoarseLowerShape.Batch0016.a129.bounds
  · rw [←r_profile129_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile129_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry129_linked.2.2.2.2.1
  · exact geometry129_linked.2.2.2.2.2
  · exact r_reference129_checked
  · exact a_reference129_checked
  · exact r_fixed129_linked
  · exact a_fixed129_linked
  · exact time129_checked
  · exact ht
  · exact hw
theorem child_geometry129_checked : ReferenceWeightData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights129 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0032.cert258∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch32_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0032.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0032.cert259∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch32_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0032.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0032.cert258.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry129_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights258_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0032.cert259.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry129_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry129_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights259_linked j (List.mem_finRange j))
theorem actual_frozen_frame129 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame129 (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.flow.timeParameter_mem child_geometry129_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights129 hz)
theorem r_profile130_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r130=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds := by rfl
theorem a_profile130_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a130=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a130.bounds := by rfl
theorem r_fixed130_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 7 := by decide +kernel
theorem a_fixed130_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a130.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.a130.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 9 := by decide +kernel
theorem ranks130_linked : ReferenceRankData.CoarseLowerShape.Batch0016.targetR130=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0016.targetA130=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 1 := by decide +kernel
theorem r_input130_linked : ReferenceRankData.CoarseLowerShape.Batch0016.r130.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds.gauge] := by decide +kernel
theorem a_input130_linked : ReferenceRankData.CoarseLowerShape.Batch0016.a130.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.a130.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.a130.bounds.gauge] := by decide +kernel
theorem geometry130_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.a := by decide +kernel
theorem weights260_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0032.cert260.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights261_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0032.cert261.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time130_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 10)=true := by decide +kernel
theorem r_reference130_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 0)=true := by decide +kernel
theorem a_reference130_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 1)=true := by decide +kernel
theorem rank_r_link130_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r130 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link130_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0016.a130.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a130 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints130 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell true ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r130 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile130_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link130_checked
    geometry130_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell false ReferenceProfileData.CoarseLowerShape.Batch0016.a130.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a130 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile130_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link130_checked
    geometry130_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks130_linked.1,←ranks130_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0016.r130.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a130.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0016.ordered130_checked hr ha ho
theorem frozen_frame130 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130 ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds ReferenceProfileData.CoarseLowerShape.Batch0016.a130.bounds
  · rw [←r_profile130_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile130_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry130_linked.2.2.2.2.1
  · exact geometry130_linked.2.2.2.2.2
  · exact r_reference130_checked
  · exact a_reference130_checked
  · exact r_fixed130_linked
  · exact a_fixed130_linked
  · exact time130_checked
  · exact ht
  · exact hw
theorem child_geometry130_checked : ReferenceWeightData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights130 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0032.cert260∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch32_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0032.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0032.cert261∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch32_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0032.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0032.cert260.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry130_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights260_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0032.cert261.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry130_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry130_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights261_linked j (List.mem_finRange j))
theorem actual_frozen_frame130 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame130 (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.flow.timeParameter_mem child_geometry130_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights130 hz)
theorem r_profile131_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r131=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds := by rfl
theorem a_profile131_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a131=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a131.bounds := by rfl
theorem r_fixed131_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 7 := by decide +kernel
theorem a_fixed131_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a131.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.a131.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 9 := by decide +kernel
theorem ranks131_linked : ReferenceRankData.CoarseLowerShape.Batch0016.targetR131=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0016.targetA131=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 1 := by decide +kernel
theorem r_input131_linked : ReferenceRankData.CoarseLowerShape.Batch0016.r131.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds.gauge] := by decide +kernel
theorem a_input131_linked : ReferenceRankData.CoarseLowerShape.Batch0016.a131.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.a131.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.a131.bounds.gauge] := by decide +kernel
theorem geometry131_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.a := by decide +kernel
theorem weights262_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0032.cert262.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights263_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0032.cert263.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time131_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 10)=true := by decide +kernel
theorem r_reference131_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 0)=true := by decide +kernel
theorem a_reference131_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 1)=true := by decide +kernel
theorem rank_r_link131_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r131 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link131_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0016.a131.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a131 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints131 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell true ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r131 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile131_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link131_checked
    geometry131_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell false ReferenceProfileData.CoarseLowerShape.Batch0016.a131.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a131 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile131_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link131_checked
    geometry131_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks131_linked.1,←ranks131_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0016.r131.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a131.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0016.ordered131_checked hr ha ho
theorem frozen_frame131 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131 ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds ReferenceProfileData.CoarseLowerShape.Batch0016.a131.bounds
  · rw [←r_profile131_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile131_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry131_linked.2.2.2.2.1
  · exact geometry131_linked.2.2.2.2.2
  · exact r_reference131_checked
  · exact a_reference131_checked
  · exact r_fixed131_linked
  · exact a_fixed131_linked
  · exact time131_checked
  · exact ht
  · exact hw
theorem child_geometry131_checked : ReferenceWeightData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights131 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0032.cert262∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch32_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0032.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0032.cert263∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch32_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0032.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0032.cert262.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry131_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights262_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0032.cert263.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry131_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry131_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights263_linked j (List.mem_finRange j))
theorem actual_frozen_frame131 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame131 (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.flow.timeParameter_mem child_geometry131_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights131 hz)
theorem r_profile132_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r132=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds := by rfl
theorem a_profile132_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a132=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a132.bounds := by rfl
theorem r_fixed132_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 7 := by decide +kernel
theorem a_fixed132_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a132.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.a132.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 9 := by decide +kernel
theorem ranks132_linked : ReferenceRankData.CoarseLowerShape.Batch0016.targetR132=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0016.targetA132=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 1 := by decide +kernel
theorem r_input132_linked : ReferenceRankData.CoarseLowerShape.Batch0016.r132.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds.gauge] := by decide +kernel
theorem a_input132_linked : ReferenceRankData.CoarseLowerShape.Batch0016.a132.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.a132.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.a132.bounds.gauge] := by decide +kernel
theorem geometry132_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.a := by decide +kernel
theorem weights264_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0033.cert264.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights265_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0033.cert265.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time132_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 10)=true := by decide +kernel
theorem r_reference132_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 0)=true := by decide +kernel
theorem a_reference132_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 1)=true := by decide +kernel
theorem rank_r_link132_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r132 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link132_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0016.a132.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a132 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints132 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell true ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r132 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile132_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link132_checked
    geometry132_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell false ReferenceProfileData.CoarseLowerShape.Batch0016.a132.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a132 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile132_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link132_checked
    geometry132_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks132_linked.1,←ranks132_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0016.r132.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a132.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0016.ordered132_checked hr ha ho
theorem frozen_frame132 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132 ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds ReferenceProfileData.CoarseLowerShape.Batch0016.a132.bounds
  · rw [←r_profile132_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile132_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry132_linked.2.2.2.2.1
  · exact geometry132_linked.2.2.2.2.2
  · exact r_reference132_checked
  · exact a_reference132_checked
  · exact r_fixed132_linked
  · exact a_fixed132_linked
  · exact time132_checked
  · exact ht
  · exact hw
theorem child_geometry132_checked : ReferenceWeightData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights132 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0033.cert264∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch33_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0033.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0033.cert265∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch33_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0033.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0033.cert264.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry132_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights264_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0033.cert265.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry132_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry132_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights265_linked j (List.mem_finRange j))
theorem actual_frozen_frame132 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame132 (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.flow.timeParameter_mem child_geometry132_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights132 hz)
theorem r_profile133_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r133=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds := by rfl
theorem a_profile133_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a133=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a133.bounds := by rfl
theorem r_fixed133_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 7 := by decide +kernel
theorem a_fixed133_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a133.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.a133.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 9 := by decide +kernel
theorem ranks133_linked : ReferenceRankData.CoarseLowerShape.Batch0016.targetR133=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0016.targetA133=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 1 := by decide +kernel
theorem r_input133_linked : ReferenceRankData.CoarseLowerShape.Batch0016.r133.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds.gauge] := by decide +kernel
theorem a_input133_linked : ReferenceRankData.CoarseLowerShape.Batch0016.a133.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.a133.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.a133.bounds.gauge] := by decide +kernel
theorem geometry133_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.a := by decide +kernel
theorem weights266_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0033.cert266.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights267_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0033.cert267.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time133_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 10)=true := by decide +kernel
theorem r_reference133_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 0)=true := by decide +kernel
theorem a_reference133_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 1)=true := by decide +kernel
theorem rank_r_link133_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r133 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link133_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0016.a133.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a133 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints133 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell true ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r133 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile133_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link133_checked
    geometry133_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell false ReferenceProfileData.CoarseLowerShape.Batch0016.a133.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a133 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile133_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link133_checked
    geometry133_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks133_linked.1,←ranks133_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0016.r133.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a133.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0016.ordered133_checked hr ha ho
theorem frozen_frame133 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133 ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds ReferenceProfileData.CoarseLowerShape.Batch0016.a133.bounds
  · rw [←r_profile133_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile133_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry133_linked.2.2.2.2.1
  · exact geometry133_linked.2.2.2.2.2
  · exact r_reference133_checked
  · exact a_reference133_checked
  · exact r_fixed133_linked
  · exact a_fixed133_linked
  · exact time133_checked
  · exact ht
  · exact hw
theorem child_geometry133_checked : ReferenceWeightData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights133 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0033.cert266∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch33_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0033.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0033.cert267∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch33_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0033.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0033.cert266.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry133_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights266_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0033.cert267.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry133_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry133_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights267_linked j (List.mem_finRange j))
theorem actual_frozen_frame133 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame133 (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.flow.timeParameter_mem child_geometry133_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights133 hz)
theorem r_profile134_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r134=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds := by rfl
theorem a_profile134_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a134=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a134.bounds := by rfl
theorem r_fixed134_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 7 := by decide +kernel
theorem a_fixed134_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a134.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.a134.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 9 := by decide +kernel
theorem ranks134_linked : ReferenceRankData.CoarseLowerShape.Batch0016.targetR134=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0016.targetA134=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 1 := by decide +kernel
theorem r_input134_linked : ReferenceRankData.CoarseLowerShape.Batch0016.r134.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds.gauge] := by decide +kernel
theorem a_input134_linked : ReferenceRankData.CoarseLowerShape.Batch0016.a134.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.a134.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.a134.bounds.gauge] := by decide +kernel
theorem geometry134_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.a := by decide +kernel
theorem weights268_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0033.cert268.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights269_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0033.cert269.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time134_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 10)=true := by decide +kernel
theorem r_reference134_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 0)=true := by decide +kernel
theorem a_reference134_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 1)=true := by decide +kernel
theorem rank_r_link134_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r134 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link134_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0016.a134.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a134 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints134 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell true ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r134 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile134_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link134_checked
    geometry134_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell false ReferenceProfileData.CoarseLowerShape.Batch0016.a134.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a134 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile134_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link134_checked
    geometry134_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks134_linked.1,←ranks134_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0016.r134.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a134.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0016.ordered134_checked hr ha ho
theorem frozen_frame134 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134 ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds ReferenceProfileData.CoarseLowerShape.Batch0016.a134.bounds
  · rw [←r_profile134_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile134_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry134_linked.2.2.2.2.1
  · exact geometry134_linked.2.2.2.2.2
  · exact r_reference134_checked
  · exact a_reference134_checked
  · exact r_fixed134_linked
  · exact a_fixed134_linked
  · exact time134_checked
  · exact ht
  · exact hw
theorem child_geometry134_checked : ReferenceWeightData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights134 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0033.cert268∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch33_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0033.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0033.cert269∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch33_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0033.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0033.cert268.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry134_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights268_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0033.cert269.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry134_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry134_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights269_linked j (List.mem_finRange j))
theorem actual_frozen_frame134 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame134 (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.flow.timeParameter_mem child_geometry134_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights134 hz)
theorem r_profile135_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r135=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds := by rfl
theorem a_profile135_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a135=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a135.bounds := by rfl
theorem r_fixed135_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 7 := by decide +kernel
theorem a_fixed135_linked : ReferenceProfileData.CoarseLowerShape.Batch0016.a135.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0016.a135.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 9 := by decide +kernel
theorem ranks135_linked : ReferenceRankData.CoarseLowerShape.Batch0016.targetR135=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0016.targetA135=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 1 := by decide +kernel
theorem r_input135_linked : ReferenceRankData.CoarseLowerShape.Batch0016.r135.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds.gauge] := by decide +kernel
theorem a_input135_linked : ReferenceRankData.CoarseLowerShape.Batch0016.a135.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0016.a135.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0016.a135.bounds.gauge] := by decide +kernel
theorem geometry135_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.a := by decide +kernel
theorem weights270_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0033.cert270.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights271_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0033.cert271.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time135_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 10)=true := by decide +kernel
theorem r_reference135_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 0)=true := by decide +kernel
theorem a_reference135_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 1)=true := by decide +kernel
theorem rank_r_link135_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r135 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link135_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0016.a135.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a135 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints135 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell true ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds ReferenceRankData.CoarseLowerShape.Batch0016.r135 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile135_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link135_checked
    geometry135_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell false ReferenceProfileData.CoarseLowerShape.Batch0016.a135.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a135 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile135_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0016.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0016.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link135_checked
    geometry135_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks135_linked.1,←ranks135_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0016.r135.bounds ReferenceRankData.CoarseLowerShape.Batch0016.a135.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0016.ordered135_checked hr ha ho
theorem frozen_frame135 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135 ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds ReferenceProfileData.CoarseLowerShape.Batch0016.a135.bounds
  · rw [←r_profile135_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile135_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry135_linked.2.2.2.2.1
  · exact geometry135_linked.2.2.2.2.2
  · exact r_reference135_checked
  · exact a_reference135_checked
  · exact r_fixed135_linked
  · exact a_fixed135_linked
  · exact time135_checked
  · exact ht
  · exact hw
theorem child_geometry135_checked : ReferenceWeightData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights135 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0033.cert270∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch33_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0033.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0033.cert271∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch33_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0033.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0033.cert270.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry135_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights270_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0033.cert271.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry135_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry135_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights271_linked j (List.mem_finRange j))
theorem actual_frozen_frame135 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame135 (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.flow.timeParameter_mem child_geometry135_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights135 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell128),(ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell129),(ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell130),(ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell131),(ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell132),(ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell133),(ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell134),(ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0016.cell135)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0016.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0016.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame128 hz
  · exact fun z hz=>actual_frozen_frame129 hz
  · exact fun z hz=>actual_frozen_frame130 hz
  · exact fun z hz=>actual_frozen_frame131 hz
  · exact fun z hz=>actual_frozen_frame132 hz
  · exact fun z hz=>actual_frozen_frame133 hz
  · exact fun z hz=>actual_frozen_frame134 hz
  · exact fun z hz=>actual_frozen_frame135 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints128 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints129 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints130 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints131 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints132 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints133 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints134 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints135 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry128_linked.1,geometry128_linked.2.1,geometry128_linked.2.2.1,geometry128_linked.2.2.2.1⟩
  · exact ⟨geometry129_linked.1,geometry129_linked.2.1,geometry129_linked.2.2.1,geometry129_linked.2.2.2.1⟩
  · exact ⟨geometry130_linked.1,geometry130_linked.2.1,geometry130_linked.2.2.1,geometry130_linked.2.2.2.1⟩
  · exact ⟨geometry131_linked.1,geometry131_linked.2.1,geometry131_linked.2.2.1,geometry131_linked.2.2.2.1⟩
  · exact ⟨geometry132_linked.1,geometry132_linked.2.1,geometry132_linked.2.2.1,geometry132_linked.2.2.2.1⟩
  · exact ⟨geometry133_linked.1,geometry133_linked.2.1,geometry133_linked.2.2.1,geometry133_linked.2.2.2.1⟩
  · exact ⟨geometry134_linked.1,geometry134_linked.2.1,geometry134_linked.2.2.1,geometry134_linked.2.2.2.1⟩
  · exact ⟨geometry135_linked.1,geometry135_linked.2.1,geometry135_linked.2.2.1,geometry135_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.a128.bounds,?_,geometry128_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a128.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile128_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds,?_,geometry128_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert128.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r128.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile128_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.a129.bounds,?_,geometry129_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a129.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile129_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds,?_,geometry129_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert129.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r129.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile129_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.a130.bounds,?_,geometry130_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a130.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile130_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds,?_,geometry130_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert130.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r130.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile130_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.a131.bounds,?_,geometry131_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a131.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile131_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds,?_,geometry131_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert131.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r131.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile131_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.a132.bounds,?_,geometry132_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a132.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile132_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds,?_,geometry132_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert132.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r132.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile132_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.a133.bounds,?_,geometry133_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a133.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile133_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds,?_,geometry133_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert133.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r133.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile133_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.a134.bounds,?_,geometry134_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a134.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile134_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds,?_,geometry134_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert134.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r134.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile134_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.a135.bounds,?_,geometry135_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0016.a135.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile135_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds,?_,geometry135_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0016.cert135.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0016.r135.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile135_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0016.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0016.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0016

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0017
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch34_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0034.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0034.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch35_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0035.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0035.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile136_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r136=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds := by rfl
theorem a_profile136_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a136=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a136.bounds := by rfl
theorem r_fixed136_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 7 := by decide +kernel
theorem a_fixed136_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a136.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.a136.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 9 := by decide +kernel
theorem ranks136_linked : ReferenceRankData.CoarseLowerShape.Batch0017.targetR136=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0017.targetA136=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 1 := by decide +kernel
theorem r_input136_linked : ReferenceRankData.CoarseLowerShape.Batch0017.r136.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds.gauge] := by decide +kernel
theorem a_input136_linked : ReferenceRankData.CoarseLowerShape.Batch0017.a136.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.a136.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.a136.bounds.gauge] := by decide +kernel
theorem geometry136_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.a := by decide +kernel
theorem weights272_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0034.cert272.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights273_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0034.cert273.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time136_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 10)=true := by decide +kernel
theorem r_reference136_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 0)=true := by decide +kernel
theorem a_reference136_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 1)=true := by decide +kernel
theorem rank_r_link136_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r136 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link136_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0017.a136.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a136 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints136 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell true ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r136 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile136_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link136_checked
    geometry136_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell false ReferenceProfileData.CoarseLowerShape.Batch0017.a136.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a136 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile136_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link136_checked
    geometry136_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks136_linked.1,←ranks136_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0017.r136.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a136.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0017.ordered136_checked hr ha ho
theorem frozen_frame136 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136 ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds ReferenceProfileData.CoarseLowerShape.Batch0017.a136.bounds
  · rw [←r_profile136_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile136_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry136_linked.2.2.2.2.1
  · exact geometry136_linked.2.2.2.2.2
  · exact r_reference136_checked
  · exact a_reference136_checked
  · exact r_fixed136_linked
  · exact a_fixed136_linked
  · exact time136_checked
  · exact ht
  · exact hw
theorem child_geometry136_checked : ReferenceWeightData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights136 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0034.cert272∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch34_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0034.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0034.cert273∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch34_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0034.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0034.cert272.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry136_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights272_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0034.cert273.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry136_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry136_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights273_linked j (List.mem_finRange j))
theorem actual_frozen_frame136 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame136 (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.flow.timeParameter_mem child_geometry136_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights136 hz)
theorem r_profile137_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r137=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds := by rfl
theorem a_profile137_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a137=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a137.bounds := by rfl
theorem r_fixed137_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 7 := by decide +kernel
theorem a_fixed137_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a137.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.a137.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 9 := by decide +kernel
theorem ranks137_linked : ReferenceRankData.CoarseLowerShape.Batch0017.targetR137=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0017.targetA137=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 1 := by decide +kernel
theorem r_input137_linked : ReferenceRankData.CoarseLowerShape.Batch0017.r137.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds.gauge] := by decide +kernel
theorem a_input137_linked : ReferenceRankData.CoarseLowerShape.Batch0017.a137.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.a137.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.a137.bounds.gauge] := by decide +kernel
theorem geometry137_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.a := by decide +kernel
theorem weights274_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0034.cert274.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights275_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0034.cert275.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time137_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 10)=true := by decide +kernel
theorem r_reference137_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 0)=true := by decide +kernel
theorem a_reference137_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 1)=true := by decide +kernel
theorem rank_r_link137_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r137 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link137_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0017.a137.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a137 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints137 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell true ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r137 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile137_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link137_checked
    geometry137_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell false ReferenceProfileData.CoarseLowerShape.Batch0017.a137.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a137 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile137_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link137_checked
    geometry137_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks137_linked.1,←ranks137_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0017.r137.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a137.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0017.ordered137_checked hr ha ho
theorem frozen_frame137 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137 ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds ReferenceProfileData.CoarseLowerShape.Batch0017.a137.bounds
  · rw [←r_profile137_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile137_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry137_linked.2.2.2.2.1
  · exact geometry137_linked.2.2.2.2.2
  · exact r_reference137_checked
  · exact a_reference137_checked
  · exact r_fixed137_linked
  · exact a_fixed137_linked
  · exact time137_checked
  · exact ht
  · exact hw
theorem child_geometry137_checked : ReferenceWeightData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights137 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0034.cert274∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch34_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0034.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0034.cert275∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch34_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0034.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0034.cert274.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry137_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights274_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0034.cert275.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry137_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry137_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights275_linked j (List.mem_finRange j))
theorem actual_frozen_frame137 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame137 (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.flow.timeParameter_mem child_geometry137_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights137 hz)
theorem r_profile138_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r138=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds := by rfl
theorem a_profile138_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a138=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a138.bounds := by rfl
theorem r_fixed138_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 7 := by decide +kernel
theorem a_fixed138_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a138.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.a138.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 9 := by decide +kernel
theorem ranks138_linked : ReferenceRankData.CoarseLowerShape.Batch0017.targetR138=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0017.targetA138=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 1 := by decide +kernel
theorem r_input138_linked : ReferenceRankData.CoarseLowerShape.Batch0017.r138.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds.gauge] := by decide +kernel
theorem a_input138_linked : ReferenceRankData.CoarseLowerShape.Batch0017.a138.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.a138.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.a138.bounds.gauge] := by decide +kernel
theorem geometry138_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.a := by decide +kernel
theorem weights276_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0034.cert276.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights277_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0034.cert277.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time138_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 10)=true := by decide +kernel
theorem r_reference138_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 0)=true := by decide +kernel
theorem a_reference138_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 1)=true := by decide +kernel
theorem rank_r_link138_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r138 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link138_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0017.a138.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a138 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints138 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell true ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r138 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile138_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link138_checked
    geometry138_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell false ReferenceProfileData.CoarseLowerShape.Batch0017.a138.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a138 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile138_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link138_checked
    geometry138_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks138_linked.1,←ranks138_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0017.r138.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a138.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0017.ordered138_checked hr ha ho
theorem frozen_frame138 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138 ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds ReferenceProfileData.CoarseLowerShape.Batch0017.a138.bounds
  · rw [←r_profile138_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile138_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry138_linked.2.2.2.2.1
  · exact geometry138_linked.2.2.2.2.2
  · exact r_reference138_checked
  · exact a_reference138_checked
  · exact r_fixed138_linked
  · exact a_fixed138_linked
  · exact time138_checked
  · exact ht
  · exact hw
theorem child_geometry138_checked : ReferenceWeightData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights138 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0034.cert276∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch34_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0034.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0034.cert277∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch34_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0034.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0034.cert276.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry138_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights276_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0034.cert277.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry138_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry138_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights277_linked j (List.mem_finRange j))
theorem actual_frozen_frame138 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame138 (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.flow.timeParameter_mem child_geometry138_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights138 hz)
theorem r_profile139_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r139=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds := by rfl
theorem a_profile139_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a139=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a139.bounds := by rfl
theorem r_fixed139_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 7 := by decide +kernel
theorem a_fixed139_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a139.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.a139.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 9 := by decide +kernel
theorem ranks139_linked : ReferenceRankData.CoarseLowerShape.Batch0017.targetR139=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0017.targetA139=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 1 := by decide +kernel
theorem r_input139_linked : ReferenceRankData.CoarseLowerShape.Batch0017.r139.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds.gauge] := by decide +kernel
theorem a_input139_linked : ReferenceRankData.CoarseLowerShape.Batch0017.a139.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.a139.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.a139.bounds.gauge] := by decide +kernel
theorem geometry139_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.a := by decide +kernel
theorem weights278_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0034.cert278.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights279_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0034.cert279.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time139_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 10)=true := by decide +kernel
theorem r_reference139_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 0)=true := by decide +kernel
theorem a_reference139_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 1)=true := by decide +kernel
theorem rank_r_link139_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r139 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link139_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0017.a139.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a139 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints139 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell true ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r139 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile139_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link139_checked
    geometry139_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell false ReferenceProfileData.CoarseLowerShape.Batch0017.a139.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a139 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile139_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link139_checked
    geometry139_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks139_linked.1,←ranks139_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0017.r139.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a139.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0017.ordered139_checked hr ha ho
theorem frozen_frame139 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139 ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds ReferenceProfileData.CoarseLowerShape.Batch0017.a139.bounds
  · rw [←r_profile139_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile139_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry139_linked.2.2.2.2.1
  · exact geometry139_linked.2.2.2.2.2
  · exact r_reference139_checked
  · exact a_reference139_checked
  · exact r_fixed139_linked
  · exact a_fixed139_linked
  · exact time139_checked
  · exact ht
  · exact hw
theorem child_geometry139_checked : ReferenceWeightData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights139 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0034.cert278∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch34_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0034.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0034.cert279∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch34_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0034.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0034.cert278.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry139_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights278_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0034.cert279.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry139_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry139_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights279_linked j (List.mem_finRange j))
theorem actual_frozen_frame139 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame139 (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.flow.timeParameter_mem child_geometry139_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights139 hz)
theorem r_profile140_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r140=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds := by rfl
theorem a_profile140_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a140=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a140.bounds := by rfl
theorem r_fixed140_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 7 := by decide +kernel
theorem a_fixed140_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a140.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.a140.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 9 := by decide +kernel
theorem ranks140_linked : ReferenceRankData.CoarseLowerShape.Batch0017.targetR140=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0017.targetA140=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 1 := by decide +kernel
theorem r_input140_linked : ReferenceRankData.CoarseLowerShape.Batch0017.r140.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds.gauge] := by decide +kernel
theorem a_input140_linked : ReferenceRankData.CoarseLowerShape.Batch0017.a140.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.a140.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.a140.bounds.gauge] := by decide +kernel
theorem geometry140_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.a := by decide +kernel
theorem weights280_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0035.cert280.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights281_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0035.cert281.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time140_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 10)=true := by decide +kernel
theorem r_reference140_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 0)=true := by decide +kernel
theorem a_reference140_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 1)=true := by decide +kernel
theorem rank_r_link140_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r140 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link140_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0017.a140.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a140 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints140 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell true ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r140 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile140_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link140_checked
    geometry140_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell false ReferenceProfileData.CoarseLowerShape.Batch0017.a140.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a140 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile140_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link140_checked
    geometry140_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks140_linked.1,←ranks140_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0017.r140.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a140.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0017.ordered140_checked hr ha ho
theorem frozen_frame140 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140 ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds ReferenceProfileData.CoarseLowerShape.Batch0017.a140.bounds
  · rw [←r_profile140_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile140_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry140_linked.2.2.2.2.1
  · exact geometry140_linked.2.2.2.2.2
  · exact r_reference140_checked
  · exact a_reference140_checked
  · exact r_fixed140_linked
  · exact a_fixed140_linked
  · exact time140_checked
  · exact ht
  · exact hw
theorem child_geometry140_checked : ReferenceWeightData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights140 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0035.cert280∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch35_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0035.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0035.cert281∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch35_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0035.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0035.cert280.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry140_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights280_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0035.cert281.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry140_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry140_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights281_linked j (List.mem_finRange j))
theorem actual_frozen_frame140 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame140 (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.flow.timeParameter_mem child_geometry140_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights140 hz)
theorem r_profile141_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r141=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds := by rfl
theorem a_profile141_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a141=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a141.bounds := by rfl
theorem r_fixed141_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 7 := by decide +kernel
theorem a_fixed141_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a141.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.a141.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 9 := by decide +kernel
theorem ranks141_linked : ReferenceRankData.CoarseLowerShape.Batch0017.targetR141=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0017.targetA141=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 1 := by decide +kernel
theorem r_input141_linked : ReferenceRankData.CoarseLowerShape.Batch0017.r141.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds.gauge] := by decide +kernel
theorem a_input141_linked : ReferenceRankData.CoarseLowerShape.Batch0017.a141.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.a141.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.a141.bounds.gauge] := by decide +kernel
theorem geometry141_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.a := by decide +kernel
theorem weights282_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0035.cert282.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights283_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0035.cert283.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time141_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 10)=true := by decide +kernel
theorem r_reference141_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 0)=true := by decide +kernel
theorem a_reference141_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 1)=true := by decide +kernel
theorem rank_r_link141_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r141 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link141_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0017.a141.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a141 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints141 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell true ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r141 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile141_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link141_checked
    geometry141_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell false ReferenceProfileData.CoarseLowerShape.Batch0017.a141.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a141 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile141_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link141_checked
    geometry141_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks141_linked.1,←ranks141_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0017.r141.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a141.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0017.ordered141_checked hr ha ho
theorem frozen_frame141 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141 ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds ReferenceProfileData.CoarseLowerShape.Batch0017.a141.bounds
  · rw [←r_profile141_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile141_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry141_linked.2.2.2.2.1
  · exact geometry141_linked.2.2.2.2.2
  · exact r_reference141_checked
  · exact a_reference141_checked
  · exact r_fixed141_linked
  · exact a_fixed141_linked
  · exact time141_checked
  · exact ht
  · exact hw
theorem child_geometry141_checked : ReferenceWeightData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights141 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0035.cert282∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch35_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0035.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0035.cert283∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch35_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0035.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0035.cert282.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry141_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights282_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0035.cert283.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry141_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry141_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights283_linked j (List.mem_finRange j))
theorem actual_frozen_frame141 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame141 (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.flow.timeParameter_mem child_geometry141_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights141 hz)
theorem r_profile142_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r142=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds := by rfl
theorem a_profile142_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a142=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a142.bounds := by rfl
theorem r_fixed142_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 7 := by decide +kernel
theorem a_fixed142_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a142.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.a142.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 9 := by decide +kernel
theorem ranks142_linked : ReferenceRankData.CoarseLowerShape.Batch0017.targetR142=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0017.targetA142=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 1 := by decide +kernel
theorem r_input142_linked : ReferenceRankData.CoarseLowerShape.Batch0017.r142.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds.gauge] := by decide +kernel
theorem a_input142_linked : ReferenceRankData.CoarseLowerShape.Batch0017.a142.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.a142.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.a142.bounds.gauge] := by decide +kernel
theorem geometry142_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.a := by decide +kernel
theorem weights284_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0035.cert284.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights285_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0035.cert285.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time142_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 10)=true := by decide +kernel
theorem r_reference142_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 0)=true := by decide +kernel
theorem a_reference142_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 1)=true := by decide +kernel
theorem rank_r_link142_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r142 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link142_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0017.a142.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a142 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints142 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell true ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r142 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile142_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link142_checked
    geometry142_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell false ReferenceProfileData.CoarseLowerShape.Batch0017.a142.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a142 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile142_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link142_checked
    geometry142_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks142_linked.1,←ranks142_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0017.r142.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a142.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0017.ordered142_checked hr ha ho
theorem frozen_frame142 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142 ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds ReferenceProfileData.CoarseLowerShape.Batch0017.a142.bounds
  · rw [←r_profile142_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile142_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry142_linked.2.2.2.2.1
  · exact geometry142_linked.2.2.2.2.2
  · exact r_reference142_checked
  · exact a_reference142_checked
  · exact r_fixed142_linked
  · exact a_fixed142_linked
  · exact time142_checked
  · exact ht
  · exact hw
theorem child_geometry142_checked : ReferenceWeightData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights142 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0035.cert284∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch35_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0035.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0035.cert285∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch35_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0035.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0035.cert284.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry142_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights284_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0035.cert285.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry142_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry142_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights285_linked j (List.mem_finRange j))
theorem actual_frozen_frame142 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame142 (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.flow.timeParameter_mem child_geometry142_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights142 hz)
theorem r_profile143_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r143=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds := by rfl
theorem a_profile143_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a143=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a143.bounds := by rfl
theorem r_fixed143_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 7 := by decide +kernel
theorem a_fixed143_linked : ReferenceProfileData.CoarseLowerShape.Batch0017.a143.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0017.a143.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 9 := by decide +kernel
theorem ranks143_linked : ReferenceRankData.CoarseLowerShape.Batch0017.targetR143=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0017.targetA143=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 1 := by decide +kernel
theorem r_input143_linked : ReferenceRankData.CoarseLowerShape.Batch0017.r143.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds.gauge] := by decide +kernel
theorem a_input143_linked : ReferenceRankData.CoarseLowerShape.Batch0017.a143.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0017.a143.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0017.a143.bounds.gauge] := by decide +kernel
theorem geometry143_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.a := by decide +kernel
theorem weights286_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0035.cert286.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights287_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0035.cert287.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time143_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 10)=true := by decide +kernel
theorem r_reference143_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 0)=true := by decide +kernel
theorem a_reference143_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 1)=true := by decide +kernel
theorem rank_r_link143_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r143 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link143_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0017.a143.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a143 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints143 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell true ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds ReferenceRankData.CoarseLowerShape.Batch0017.r143 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile143_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link143_checked
    geometry143_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell false ReferenceProfileData.CoarseLowerShape.Batch0017.a143.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a143 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile143_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0017.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0017.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link143_checked
    geometry143_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks143_linked.1,←ranks143_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0017.r143.bounds ReferenceRankData.CoarseLowerShape.Batch0017.a143.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0017.ordered143_checked hr ha ho
theorem frozen_frame143 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143 ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds ReferenceProfileData.CoarseLowerShape.Batch0017.a143.bounds
  · rw [←r_profile143_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile143_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry143_linked.2.2.2.2.1
  · exact geometry143_linked.2.2.2.2.2
  · exact r_reference143_checked
  · exact a_reference143_checked
  · exact r_fixed143_linked
  · exact a_fixed143_linked
  · exact time143_checked
  · exact ht
  · exact hw
theorem child_geometry143_checked : ReferenceWeightData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights143 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0035.cert286∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch35_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0035.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0035.cert287∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch35_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0035.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0035.cert286.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry143_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights286_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0035.cert287.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry143_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry143_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights287_linked j (List.mem_finRange j))
theorem actual_frozen_frame143 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame143 (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.flow.timeParameter_mem child_geometry143_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights143 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell136),(ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell137),(ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell138),(ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell139),(ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell140),(ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell141),(ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell142),(ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0017.cell143)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0017.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0017.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame136 hz
  · exact fun z hz=>actual_frozen_frame137 hz
  · exact fun z hz=>actual_frozen_frame138 hz
  · exact fun z hz=>actual_frozen_frame139 hz
  · exact fun z hz=>actual_frozen_frame140 hz
  · exact fun z hz=>actual_frozen_frame141 hz
  · exact fun z hz=>actual_frozen_frame142 hz
  · exact fun z hz=>actual_frozen_frame143 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints136 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints137 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints138 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints139 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints140 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints141 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints142 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints143 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry136_linked.1,geometry136_linked.2.1,geometry136_linked.2.2.1,geometry136_linked.2.2.2.1⟩
  · exact ⟨geometry137_linked.1,geometry137_linked.2.1,geometry137_linked.2.2.1,geometry137_linked.2.2.2.1⟩
  · exact ⟨geometry138_linked.1,geometry138_linked.2.1,geometry138_linked.2.2.1,geometry138_linked.2.2.2.1⟩
  · exact ⟨geometry139_linked.1,geometry139_linked.2.1,geometry139_linked.2.2.1,geometry139_linked.2.2.2.1⟩
  · exact ⟨geometry140_linked.1,geometry140_linked.2.1,geometry140_linked.2.2.1,geometry140_linked.2.2.2.1⟩
  · exact ⟨geometry141_linked.1,geometry141_linked.2.1,geometry141_linked.2.2.1,geometry141_linked.2.2.2.1⟩
  · exact ⟨geometry142_linked.1,geometry142_linked.2.1,geometry142_linked.2.2.1,geometry142_linked.2.2.2.1⟩
  · exact ⟨geometry143_linked.1,geometry143_linked.2.1,geometry143_linked.2.2.1,geometry143_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.a136.bounds,?_,geometry136_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a136.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile136_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds,?_,geometry136_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert136.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r136.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile136_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.a137.bounds,?_,geometry137_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a137.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile137_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds,?_,geometry137_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert137.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r137.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile137_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.a138.bounds,?_,geometry138_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a138.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile138_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds,?_,geometry138_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert138.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r138.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile138_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.a139.bounds,?_,geometry139_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a139.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile139_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds,?_,geometry139_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert139.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r139.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile139_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.a140.bounds,?_,geometry140_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a140.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile140_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds,?_,geometry140_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert140.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r140.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile140_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.a141.bounds,?_,geometry141_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a141.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile141_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds,?_,geometry141_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert141.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r141.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile141_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.a142.bounds,?_,geometry142_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a142.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile142_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds,?_,geometry142_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert142.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r142.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile142_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.a143.bounds,?_,geometry143_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0017.a143.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile143_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds,?_,geometry143_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0017.cert143.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0017.r143.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile143_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0017.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0017.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0017

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0018
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch36_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0036.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0036.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch37_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0037.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0037.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile144_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r144=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds := by rfl
theorem a_profile144_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a144=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a144.bounds := by rfl
theorem r_fixed144_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 7 := by decide +kernel
theorem a_fixed144_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a144.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.a144.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 9 := by decide +kernel
theorem ranks144_linked : ReferenceRankData.CoarseLowerShape.Batch0018.targetR144=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0018.targetA144=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 1 := by decide +kernel
theorem r_input144_linked : ReferenceRankData.CoarseLowerShape.Batch0018.r144.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds.gauge] := by decide +kernel
theorem a_input144_linked : ReferenceRankData.CoarseLowerShape.Batch0018.a144.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.a144.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.a144.bounds.gauge] := by decide +kernel
theorem geometry144_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.a := by decide +kernel
theorem weights288_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0036.cert288.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights289_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0036.cert289.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time144_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 10)=true := by decide +kernel
theorem r_reference144_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 0)=true := by decide +kernel
theorem a_reference144_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 1)=true := by decide +kernel
theorem rank_r_link144_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r144 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link144_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0018.a144.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a144 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints144 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell true ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r144 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile144_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link144_checked
    geometry144_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell false ReferenceProfileData.CoarseLowerShape.Batch0018.a144.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a144 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile144_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link144_checked
    geometry144_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks144_linked.1,←ranks144_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0018.r144.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a144.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0018.ordered144_checked hr ha ho
theorem frozen_frame144 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144 ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds ReferenceProfileData.CoarseLowerShape.Batch0018.a144.bounds
  · rw [←r_profile144_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile144_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry144_linked.2.2.2.2.1
  · exact geometry144_linked.2.2.2.2.2
  · exact r_reference144_checked
  · exact a_reference144_checked
  · exact r_fixed144_linked
  · exact a_fixed144_linked
  · exact time144_checked
  · exact ht
  · exact hw
theorem child_geometry144_checked : ReferenceWeightData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights144 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0036.cert288∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch36_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0036.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0036.cert289∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch36_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0036.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0036.cert288.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry144_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights288_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0036.cert289.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry144_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry144_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights289_linked j (List.mem_finRange j))
theorem actual_frozen_frame144 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame144 (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.flow.timeParameter_mem child_geometry144_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights144 hz)
theorem r_profile145_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r145=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds := by rfl
theorem a_profile145_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a145=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a145.bounds := by rfl
theorem r_fixed145_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 7 := by decide +kernel
theorem a_fixed145_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a145.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.a145.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 9 := by decide +kernel
theorem ranks145_linked : ReferenceRankData.CoarseLowerShape.Batch0018.targetR145=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0018.targetA145=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 1 := by decide +kernel
theorem r_input145_linked : ReferenceRankData.CoarseLowerShape.Batch0018.r145.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds.gauge] := by decide +kernel
theorem a_input145_linked : ReferenceRankData.CoarseLowerShape.Batch0018.a145.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.a145.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.a145.bounds.gauge] := by decide +kernel
theorem geometry145_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.a := by decide +kernel
theorem weights290_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0036.cert290.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights291_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0036.cert291.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time145_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 10)=true := by decide +kernel
theorem r_reference145_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 0)=true := by decide +kernel
theorem a_reference145_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 1)=true := by decide +kernel
theorem rank_r_link145_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r145 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link145_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0018.a145.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a145 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints145 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell true ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r145 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile145_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link145_checked
    geometry145_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell false ReferenceProfileData.CoarseLowerShape.Batch0018.a145.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a145 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile145_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link145_checked
    geometry145_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks145_linked.1,←ranks145_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0018.r145.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a145.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0018.ordered145_checked hr ha ho
theorem frozen_frame145 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145 ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds ReferenceProfileData.CoarseLowerShape.Batch0018.a145.bounds
  · rw [←r_profile145_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile145_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry145_linked.2.2.2.2.1
  · exact geometry145_linked.2.2.2.2.2
  · exact r_reference145_checked
  · exact a_reference145_checked
  · exact r_fixed145_linked
  · exact a_fixed145_linked
  · exact time145_checked
  · exact ht
  · exact hw
theorem child_geometry145_checked : ReferenceWeightData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights145 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0036.cert290∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch36_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0036.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0036.cert291∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch36_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0036.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0036.cert290.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry145_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights290_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0036.cert291.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry145_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry145_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights291_linked j (List.mem_finRange j))
theorem actual_frozen_frame145 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame145 (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.flow.timeParameter_mem child_geometry145_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights145 hz)
theorem r_profile146_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r146=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds := by rfl
theorem a_profile146_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a146=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a146.bounds := by rfl
theorem r_fixed146_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 7 := by decide +kernel
theorem a_fixed146_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a146.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.a146.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 9 := by decide +kernel
theorem ranks146_linked : ReferenceRankData.CoarseLowerShape.Batch0018.targetR146=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0018.targetA146=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 1 := by decide +kernel
theorem r_input146_linked : ReferenceRankData.CoarseLowerShape.Batch0018.r146.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds.gauge] := by decide +kernel
theorem a_input146_linked : ReferenceRankData.CoarseLowerShape.Batch0018.a146.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.a146.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.a146.bounds.gauge] := by decide +kernel
theorem geometry146_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.a := by decide +kernel
theorem weights292_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0036.cert292.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights293_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0036.cert293.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time146_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 10)=true := by decide +kernel
theorem r_reference146_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 0)=true := by decide +kernel
theorem a_reference146_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 1)=true := by decide +kernel
theorem rank_r_link146_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r146 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link146_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0018.a146.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a146 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints146 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell true ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r146 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile146_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link146_checked
    geometry146_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell false ReferenceProfileData.CoarseLowerShape.Batch0018.a146.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a146 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile146_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link146_checked
    geometry146_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks146_linked.1,←ranks146_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0018.r146.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a146.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0018.ordered146_checked hr ha ho
theorem frozen_frame146 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146 ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds ReferenceProfileData.CoarseLowerShape.Batch0018.a146.bounds
  · rw [←r_profile146_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile146_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry146_linked.2.2.2.2.1
  · exact geometry146_linked.2.2.2.2.2
  · exact r_reference146_checked
  · exact a_reference146_checked
  · exact r_fixed146_linked
  · exact a_fixed146_linked
  · exact time146_checked
  · exact ht
  · exact hw
theorem child_geometry146_checked : ReferenceWeightData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights146 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0036.cert292∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch36_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0036.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0036.cert293∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch36_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0036.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0036.cert292.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry146_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights292_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0036.cert293.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry146_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry146_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights293_linked j (List.mem_finRange j))
theorem actual_frozen_frame146 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame146 (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.flow.timeParameter_mem child_geometry146_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights146 hz)
theorem r_profile147_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r147=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds := by rfl
theorem a_profile147_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a147=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a147.bounds := by rfl
theorem r_fixed147_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 7 := by decide +kernel
theorem a_fixed147_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a147.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.a147.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 9 := by decide +kernel
theorem ranks147_linked : ReferenceRankData.CoarseLowerShape.Batch0018.targetR147=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0018.targetA147=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 1 := by decide +kernel
theorem r_input147_linked : ReferenceRankData.CoarseLowerShape.Batch0018.r147.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds.gauge] := by decide +kernel
theorem a_input147_linked : ReferenceRankData.CoarseLowerShape.Batch0018.a147.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.a147.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.a147.bounds.gauge] := by decide +kernel
theorem geometry147_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.a := by decide +kernel
theorem weights294_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0036.cert294.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights295_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0036.cert295.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time147_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 10)=true := by decide +kernel
theorem r_reference147_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 0)=true := by decide +kernel
theorem a_reference147_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 1)=true := by decide +kernel
theorem rank_r_link147_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r147 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link147_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0018.a147.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a147 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints147 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell true ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r147 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile147_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link147_checked
    geometry147_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell false ReferenceProfileData.CoarseLowerShape.Batch0018.a147.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a147 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile147_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link147_checked
    geometry147_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks147_linked.1,←ranks147_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0018.r147.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a147.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0018.ordered147_checked hr ha ho
theorem frozen_frame147 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147 ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds ReferenceProfileData.CoarseLowerShape.Batch0018.a147.bounds
  · rw [←r_profile147_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile147_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry147_linked.2.2.2.2.1
  · exact geometry147_linked.2.2.2.2.2
  · exact r_reference147_checked
  · exact a_reference147_checked
  · exact r_fixed147_linked
  · exact a_fixed147_linked
  · exact time147_checked
  · exact ht
  · exact hw
theorem child_geometry147_checked : ReferenceWeightData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights147 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0036.cert294∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch36_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0036.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0036.cert295∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch36_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0036.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0036.cert294.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry147_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights294_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0036.cert295.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry147_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry147_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights295_linked j (List.mem_finRange j))
theorem actual_frozen_frame147 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame147 (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.flow.timeParameter_mem child_geometry147_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights147 hz)
theorem r_profile148_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r148=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds := by rfl
theorem a_profile148_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a148=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a148.bounds := by rfl
theorem r_fixed148_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 7 := by decide +kernel
theorem a_fixed148_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a148.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.a148.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 9 := by decide +kernel
theorem ranks148_linked : ReferenceRankData.CoarseLowerShape.Batch0018.targetR148=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0018.targetA148=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 1 := by decide +kernel
theorem r_input148_linked : ReferenceRankData.CoarseLowerShape.Batch0018.r148.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds.gauge] := by decide +kernel
theorem a_input148_linked : ReferenceRankData.CoarseLowerShape.Batch0018.a148.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.a148.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.a148.bounds.gauge] := by decide +kernel
theorem geometry148_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.a := by decide +kernel
theorem weights296_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0037.cert296.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights297_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0037.cert297.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time148_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 10)=true := by decide +kernel
theorem r_reference148_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 0)=true := by decide +kernel
theorem a_reference148_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 1)=true := by decide +kernel
theorem rank_r_link148_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r148 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link148_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0018.a148.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a148 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints148 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell true ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r148 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile148_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link148_checked
    geometry148_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell false ReferenceProfileData.CoarseLowerShape.Batch0018.a148.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a148 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile148_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link148_checked
    geometry148_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks148_linked.1,←ranks148_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0018.r148.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a148.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0018.ordered148_checked hr ha ho
theorem frozen_frame148 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148 ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds ReferenceProfileData.CoarseLowerShape.Batch0018.a148.bounds
  · rw [←r_profile148_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile148_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry148_linked.2.2.2.2.1
  · exact geometry148_linked.2.2.2.2.2
  · exact r_reference148_checked
  · exact a_reference148_checked
  · exact r_fixed148_linked
  · exact a_fixed148_linked
  · exact time148_checked
  · exact ht
  · exact hw
theorem child_geometry148_checked : ReferenceWeightData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights148 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0037.cert296∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch37_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0037.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0037.cert297∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch37_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0037.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0037.cert296.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry148_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights296_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0037.cert297.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry148_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry148_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights297_linked j (List.mem_finRange j))
theorem actual_frozen_frame148 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame148 (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.flow.timeParameter_mem child_geometry148_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights148 hz)
theorem r_profile149_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r149=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds := by rfl
theorem a_profile149_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a149=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a149.bounds := by rfl
theorem r_fixed149_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 7 := by decide +kernel
theorem a_fixed149_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a149.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.a149.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 9 := by decide +kernel
theorem ranks149_linked : ReferenceRankData.CoarseLowerShape.Batch0018.targetR149=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0018.targetA149=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 1 := by decide +kernel
theorem r_input149_linked : ReferenceRankData.CoarseLowerShape.Batch0018.r149.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds.gauge] := by decide +kernel
theorem a_input149_linked : ReferenceRankData.CoarseLowerShape.Batch0018.a149.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.a149.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.a149.bounds.gauge] := by decide +kernel
theorem geometry149_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.a := by decide +kernel
theorem weights298_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0037.cert298.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights299_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0037.cert299.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time149_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 10)=true := by decide +kernel
theorem r_reference149_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 0)=true := by decide +kernel
theorem a_reference149_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 1)=true := by decide +kernel
theorem rank_r_link149_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r149 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link149_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0018.a149.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a149 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints149 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell true ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r149 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile149_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link149_checked
    geometry149_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell false ReferenceProfileData.CoarseLowerShape.Batch0018.a149.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a149 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile149_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link149_checked
    geometry149_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks149_linked.1,←ranks149_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0018.r149.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a149.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0018.ordered149_checked hr ha ho
theorem frozen_frame149 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149 ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds ReferenceProfileData.CoarseLowerShape.Batch0018.a149.bounds
  · rw [←r_profile149_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile149_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry149_linked.2.2.2.2.1
  · exact geometry149_linked.2.2.2.2.2
  · exact r_reference149_checked
  · exact a_reference149_checked
  · exact r_fixed149_linked
  · exact a_fixed149_linked
  · exact time149_checked
  · exact ht
  · exact hw
theorem child_geometry149_checked : ReferenceWeightData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights149 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0037.cert298∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch37_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0037.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0037.cert299∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch37_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0037.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0037.cert298.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry149_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights298_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0037.cert299.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry149_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry149_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights299_linked j (List.mem_finRange j))
theorem actual_frozen_frame149 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame149 (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.flow.timeParameter_mem child_geometry149_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights149 hz)
theorem r_profile150_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r150=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds := by rfl
theorem a_profile150_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a150=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a150.bounds := by rfl
theorem r_fixed150_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 7 := by decide +kernel
theorem a_fixed150_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a150.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.a150.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 9 := by decide +kernel
theorem ranks150_linked : ReferenceRankData.CoarseLowerShape.Batch0018.targetR150=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0018.targetA150=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 1 := by decide +kernel
theorem r_input150_linked : ReferenceRankData.CoarseLowerShape.Batch0018.r150.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds.gauge] := by decide +kernel
theorem a_input150_linked : ReferenceRankData.CoarseLowerShape.Batch0018.a150.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.a150.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.a150.bounds.gauge] := by decide +kernel
theorem geometry150_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.a := by decide +kernel
theorem weights300_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0037.cert300.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights301_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0037.cert301.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time150_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 10)=true := by decide +kernel
theorem r_reference150_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 0)=true := by decide +kernel
theorem a_reference150_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 1)=true := by decide +kernel
theorem rank_r_link150_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r150 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link150_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0018.a150.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a150 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints150 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell true ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r150 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile150_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link150_checked
    geometry150_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell false ReferenceProfileData.CoarseLowerShape.Batch0018.a150.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a150 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile150_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link150_checked
    geometry150_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks150_linked.1,←ranks150_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0018.r150.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a150.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0018.ordered150_checked hr ha ho
theorem frozen_frame150 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150 ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds ReferenceProfileData.CoarseLowerShape.Batch0018.a150.bounds
  · rw [←r_profile150_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile150_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry150_linked.2.2.2.2.1
  · exact geometry150_linked.2.2.2.2.2
  · exact r_reference150_checked
  · exact a_reference150_checked
  · exact r_fixed150_linked
  · exact a_fixed150_linked
  · exact time150_checked
  · exact ht
  · exact hw
theorem child_geometry150_checked : ReferenceWeightData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights150 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0037.cert300∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch37_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0037.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0037.cert301∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch37_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0037.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0037.cert300.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry150_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights300_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0037.cert301.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry150_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry150_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights301_linked j (List.mem_finRange j))
theorem actual_frozen_frame150 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame150 (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.flow.timeParameter_mem child_geometry150_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights150 hz)
theorem r_profile151_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r151=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds := by rfl
theorem a_profile151_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a151=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a151.bounds := by rfl
theorem r_fixed151_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 7 := by decide +kernel
theorem a_fixed151_linked : ReferenceProfileData.CoarseLowerShape.Batch0018.a151.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0018.a151.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 9 := by decide +kernel
theorem ranks151_linked : ReferenceRankData.CoarseLowerShape.Batch0018.targetR151=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0018.targetA151=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 1 := by decide +kernel
theorem r_input151_linked : ReferenceRankData.CoarseLowerShape.Batch0018.r151.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds.gauge] := by decide +kernel
theorem a_input151_linked : ReferenceRankData.CoarseLowerShape.Batch0018.a151.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0018.a151.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0018.a151.bounds.gauge] := by decide +kernel
theorem geometry151_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.a := by decide +kernel
theorem weights302_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0037.cert302.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights303_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0037.cert303.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time151_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 10)=true := by decide +kernel
theorem r_reference151_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 0)=true := by decide +kernel
theorem a_reference151_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 1)=true := by decide +kernel
theorem rank_r_link151_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r151 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link151_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0018.a151.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a151 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints151 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell true ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds ReferenceRankData.CoarseLowerShape.Batch0018.r151 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile151_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link151_checked
    geometry151_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell false ReferenceProfileData.CoarseLowerShape.Batch0018.a151.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a151 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile151_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0018.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0018.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link151_checked
    geometry151_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks151_linked.1,←ranks151_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0018.r151.bounds ReferenceRankData.CoarseLowerShape.Batch0018.a151.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0018.ordered151_checked hr ha ho
theorem frozen_frame151 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151 ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds ReferenceProfileData.CoarseLowerShape.Batch0018.a151.bounds
  · rw [←r_profile151_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile151_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry151_linked.2.2.2.2.1
  · exact geometry151_linked.2.2.2.2.2
  · exact r_reference151_checked
  · exact a_reference151_checked
  · exact r_fixed151_linked
  · exact a_fixed151_linked
  · exact time151_checked
  · exact ht
  · exact hw
theorem child_geometry151_checked : ReferenceWeightData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights151 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0037.cert302∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch37_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0037.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0037.cert303∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch37_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0037.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0037.cert302.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry151_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights302_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0037.cert303.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry151_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry151_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights303_linked j (List.mem_finRange j))
theorem actual_frozen_frame151 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame151 (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.flow.timeParameter_mem child_geometry151_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights151 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell144),(ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell145),(ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell146),(ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell147),(ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell148),(ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell149),(ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell150),(ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0018.cell151)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0018.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0018.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame144 hz
  · exact fun z hz=>actual_frozen_frame145 hz
  · exact fun z hz=>actual_frozen_frame146 hz
  · exact fun z hz=>actual_frozen_frame147 hz
  · exact fun z hz=>actual_frozen_frame148 hz
  · exact fun z hz=>actual_frozen_frame149 hz
  · exact fun z hz=>actual_frozen_frame150 hz
  · exact fun z hz=>actual_frozen_frame151 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints144 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints145 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints146 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints147 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints148 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints149 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints150 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints151 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry144_linked.1,geometry144_linked.2.1,geometry144_linked.2.2.1,geometry144_linked.2.2.2.1⟩
  · exact ⟨geometry145_linked.1,geometry145_linked.2.1,geometry145_linked.2.2.1,geometry145_linked.2.2.2.1⟩
  · exact ⟨geometry146_linked.1,geometry146_linked.2.1,geometry146_linked.2.2.1,geometry146_linked.2.2.2.1⟩
  · exact ⟨geometry147_linked.1,geometry147_linked.2.1,geometry147_linked.2.2.1,geometry147_linked.2.2.2.1⟩
  · exact ⟨geometry148_linked.1,geometry148_linked.2.1,geometry148_linked.2.2.1,geometry148_linked.2.2.2.1⟩
  · exact ⟨geometry149_linked.1,geometry149_linked.2.1,geometry149_linked.2.2.1,geometry149_linked.2.2.2.1⟩
  · exact ⟨geometry150_linked.1,geometry150_linked.2.1,geometry150_linked.2.2.1,geometry150_linked.2.2.2.1⟩
  · exact ⟨geometry151_linked.1,geometry151_linked.2.1,geometry151_linked.2.2.1,geometry151_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.a144.bounds,?_,geometry144_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a144.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile144_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds,?_,geometry144_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert144.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r144.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile144_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.a145.bounds,?_,geometry145_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a145.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile145_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds,?_,geometry145_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert145.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r145.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile145_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.a146.bounds,?_,geometry146_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a146.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile146_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds,?_,geometry146_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert146.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r146.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile146_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.a147.bounds,?_,geometry147_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a147.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile147_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds,?_,geometry147_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert147.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r147.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile147_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.a148.bounds,?_,geometry148_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a148.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile148_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds,?_,geometry148_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert148.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r148.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile148_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.a149.bounds,?_,geometry149_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a149.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile149_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds,?_,geometry149_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert149.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r149.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile149_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.a150.bounds,?_,geometry150_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a150.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile150_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds,?_,geometry150_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert150.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r150.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile150_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.a151.bounds,?_,geometry151_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0018.a151.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile151_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds,?_,geometry151_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0018.cert151.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0018.r151.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile151_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0018.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0018.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0018

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0019
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch38_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0038.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0038.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch39_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0039.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0039.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile152_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r152=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds := by rfl
theorem a_profile152_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a152=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a152.bounds := by rfl
theorem r_fixed152_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 7 := by decide +kernel
theorem a_fixed152_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a152.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.a152.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 9 := by decide +kernel
theorem ranks152_linked : ReferenceRankData.CoarseLowerShape.Batch0019.targetR152=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0019.targetA152=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 1 := by decide +kernel
theorem r_input152_linked : ReferenceRankData.CoarseLowerShape.Batch0019.r152.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds.gauge] := by decide +kernel
theorem a_input152_linked : ReferenceRankData.CoarseLowerShape.Batch0019.a152.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.a152.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.a152.bounds.gauge] := by decide +kernel
theorem geometry152_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.a := by decide +kernel
theorem weights304_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0038.cert304.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights305_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0038.cert305.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time152_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 10)=true := by decide +kernel
theorem r_reference152_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 0)=true := by decide +kernel
theorem a_reference152_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 1)=true := by decide +kernel
theorem rank_r_link152_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r152 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link152_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0019.a152.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a152 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints152 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell true ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r152 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile152_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link152_checked
    geometry152_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell false ReferenceProfileData.CoarseLowerShape.Batch0019.a152.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a152 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile152_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link152_checked
    geometry152_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks152_linked.1,←ranks152_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0019.r152.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a152.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0019.ordered152_checked hr ha ho
theorem frozen_frame152 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152 ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds ReferenceProfileData.CoarseLowerShape.Batch0019.a152.bounds
  · rw [←r_profile152_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile152_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry152_linked.2.2.2.2.1
  · exact geometry152_linked.2.2.2.2.2
  · exact r_reference152_checked
  · exact a_reference152_checked
  · exact r_fixed152_linked
  · exact a_fixed152_linked
  · exact time152_checked
  · exact ht
  · exact hw
theorem child_geometry152_checked : ReferenceWeightData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights152 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0038.cert304∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch38_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0038.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0038.cert305∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch38_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0038.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0038.cert304.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry152_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights304_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0038.cert305.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry152_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry152_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights305_linked j (List.mem_finRange j))
theorem actual_frozen_frame152 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame152 (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.flow.timeParameter_mem child_geometry152_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights152 hz)
theorem r_profile153_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r153=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds := by rfl
theorem a_profile153_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a153=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a153.bounds := by rfl
theorem r_fixed153_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 7 := by decide +kernel
theorem a_fixed153_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a153.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.a153.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 9 := by decide +kernel
theorem ranks153_linked : ReferenceRankData.CoarseLowerShape.Batch0019.targetR153=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0019.targetA153=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 1 := by decide +kernel
theorem r_input153_linked : ReferenceRankData.CoarseLowerShape.Batch0019.r153.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds.gauge] := by decide +kernel
theorem a_input153_linked : ReferenceRankData.CoarseLowerShape.Batch0019.a153.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.a153.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.a153.bounds.gauge] := by decide +kernel
theorem geometry153_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.a := by decide +kernel
theorem weights306_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0038.cert306.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights307_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0038.cert307.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time153_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 10)=true := by decide +kernel
theorem r_reference153_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 0)=true := by decide +kernel
theorem a_reference153_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 1)=true := by decide +kernel
theorem rank_r_link153_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r153 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link153_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0019.a153.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a153 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints153 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell true ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r153 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile153_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link153_checked
    geometry153_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell false ReferenceProfileData.CoarseLowerShape.Batch0019.a153.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a153 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile153_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link153_checked
    geometry153_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks153_linked.1,←ranks153_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0019.r153.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a153.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0019.ordered153_checked hr ha ho
theorem frozen_frame153 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153 ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds ReferenceProfileData.CoarseLowerShape.Batch0019.a153.bounds
  · rw [←r_profile153_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile153_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry153_linked.2.2.2.2.1
  · exact geometry153_linked.2.2.2.2.2
  · exact r_reference153_checked
  · exact a_reference153_checked
  · exact r_fixed153_linked
  · exact a_fixed153_linked
  · exact time153_checked
  · exact ht
  · exact hw
theorem child_geometry153_checked : ReferenceWeightData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights153 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0038.cert306∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch38_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0038.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0038.cert307∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch38_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0038.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0038.cert306.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry153_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights306_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0038.cert307.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry153_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry153_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights307_linked j (List.mem_finRange j))
theorem actual_frozen_frame153 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame153 (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.flow.timeParameter_mem child_geometry153_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights153 hz)
theorem r_profile154_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r154=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds := by rfl
theorem a_profile154_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a154=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a154.bounds := by rfl
theorem r_fixed154_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 7 := by decide +kernel
theorem a_fixed154_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a154.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.a154.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 9 := by decide +kernel
theorem ranks154_linked : ReferenceRankData.CoarseLowerShape.Batch0019.targetR154=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0019.targetA154=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 1 := by decide +kernel
theorem r_input154_linked : ReferenceRankData.CoarseLowerShape.Batch0019.r154.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds.gauge] := by decide +kernel
theorem a_input154_linked : ReferenceRankData.CoarseLowerShape.Batch0019.a154.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.a154.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.a154.bounds.gauge] := by decide +kernel
theorem geometry154_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.a := by decide +kernel
theorem weights308_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0038.cert308.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights309_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0038.cert309.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time154_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 10)=true := by decide +kernel
theorem r_reference154_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 0)=true := by decide +kernel
theorem a_reference154_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 1)=true := by decide +kernel
theorem rank_r_link154_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r154 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link154_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0019.a154.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a154 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints154 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell true ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r154 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile154_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link154_checked
    geometry154_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell false ReferenceProfileData.CoarseLowerShape.Batch0019.a154.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a154 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile154_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link154_checked
    geometry154_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks154_linked.1,←ranks154_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0019.r154.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a154.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0019.ordered154_checked hr ha ho
theorem frozen_frame154 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154 ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds ReferenceProfileData.CoarseLowerShape.Batch0019.a154.bounds
  · rw [←r_profile154_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile154_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry154_linked.2.2.2.2.1
  · exact geometry154_linked.2.2.2.2.2
  · exact r_reference154_checked
  · exact a_reference154_checked
  · exact r_fixed154_linked
  · exact a_fixed154_linked
  · exact time154_checked
  · exact ht
  · exact hw
theorem child_geometry154_checked : ReferenceWeightData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights154 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0038.cert308∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch38_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0038.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0038.cert309∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch38_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0038.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0038.cert308.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry154_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights308_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0038.cert309.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry154_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry154_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights309_linked j (List.mem_finRange j))
theorem actual_frozen_frame154 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame154 (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.flow.timeParameter_mem child_geometry154_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights154 hz)
theorem r_profile155_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r155=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds := by rfl
theorem a_profile155_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a155=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a155.bounds := by rfl
theorem r_fixed155_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 7 := by decide +kernel
theorem a_fixed155_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a155.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.a155.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 9 := by decide +kernel
theorem ranks155_linked : ReferenceRankData.CoarseLowerShape.Batch0019.targetR155=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0019.targetA155=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 1 := by decide +kernel
theorem r_input155_linked : ReferenceRankData.CoarseLowerShape.Batch0019.r155.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds.gauge] := by decide +kernel
theorem a_input155_linked : ReferenceRankData.CoarseLowerShape.Batch0019.a155.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.a155.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.a155.bounds.gauge] := by decide +kernel
theorem geometry155_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.a := by decide +kernel
theorem weights310_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0038.cert310.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights311_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0038.cert311.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time155_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 10)=true := by decide +kernel
theorem r_reference155_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 0)=true := by decide +kernel
theorem a_reference155_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 1)=true := by decide +kernel
theorem rank_r_link155_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r155 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link155_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0019.a155.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a155 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints155 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell true ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r155 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile155_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link155_checked
    geometry155_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell false ReferenceProfileData.CoarseLowerShape.Batch0019.a155.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a155 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile155_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link155_checked
    geometry155_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks155_linked.1,←ranks155_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0019.r155.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a155.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0019.ordered155_checked hr ha ho
theorem frozen_frame155 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155 ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds ReferenceProfileData.CoarseLowerShape.Batch0019.a155.bounds
  · rw [←r_profile155_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile155_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry155_linked.2.2.2.2.1
  · exact geometry155_linked.2.2.2.2.2
  · exact r_reference155_checked
  · exact a_reference155_checked
  · exact r_fixed155_linked
  · exact a_fixed155_linked
  · exact time155_checked
  · exact ht
  · exact hw
theorem child_geometry155_checked : ReferenceWeightData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights155 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0038.cert310∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch38_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0038.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0038.cert311∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch38_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0038.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0038.cert310.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry155_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights310_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0038.cert311.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry155_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry155_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights311_linked j (List.mem_finRange j))
theorem actual_frozen_frame155 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame155 (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.flow.timeParameter_mem child_geometry155_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights155 hz)
theorem r_profile156_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r156=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds := by rfl
theorem a_profile156_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a156=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a156.bounds := by rfl
theorem r_fixed156_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 7 := by decide +kernel
theorem a_fixed156_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a156.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.a156.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 9 := by decide +kernel
theorem ranks156_linked : ReferenceRankData.CoarseLowerShape.Batch0019.targetR156=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0019.targetA156=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 1 := by decide +kernel
theorem r_input156_linked : ReferenceRankData.CoarseLowerShape.Batch0019.r156.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds.gauge] := by decide +kernel
theorem a_input156_linked : ReferenceRankData.CoarseLowerShape.Batch0019.a156.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.a156.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.a156.bounds.gauge] := by decide +kernel
theorem geometry156_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.a := by decide +kernel
theorem weights312_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0039.cert312.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights313_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0039.cert313.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time156_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 10)=true := by decide +kernel
theorem r_reference156_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 0)=true := by decide +kernel
theorem a_reference156_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 1)=true := by decide +kernel
theorem rank_r_link156_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r156 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link156_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0019.a156.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a156 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints156 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell true ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r156 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile156_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link156_checked
    geometry156_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell false ReferenceProfileData.CoarseLowerShape.Batch0019.a156.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a156 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile156_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link156_checked
    geometry156_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks156_linked.1,←ranks156_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0019.r156.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a156.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0019.ordered156_checked hr ha ho
theorem frozen_frame156 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156 ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds ReferenceProfileData.CoarseLowerShape.Batch0019.a156.bounds
  · rw [←r_profile156_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile156_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry156_linked.2.2.2.2.1
  · exact geometry156_linked.2.2.2.2.2
  · exact r_reference156_checked
  · exact a_reference156_checked
  · exact r_fixed156_linked
  · exact a_fixed156_linked
  · exact time156_checked
  · exact ht
  · exact hw
theorem child_geometry156_checked : ReferenceWeightData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights156 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0039.cert312∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch39_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0039.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0039.cert313∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch39_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0039.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0039.cert312.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry156_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights312_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0039.cert313.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry156_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry156_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights313_linked j (List.mem_finRange j))
theorem actual_frozen_frame156 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame156 (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.flow.timeParameter_mem child_geometry156_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights156 hz)
theorem r_profile157_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r157=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds := by rfl
theorem a_profile157_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a157=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a157.bounds := by rfl
theorem r_fixed157_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 7 := by decide +kernel
theorem a_fixed157_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a157.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.a157.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 9 := by decide +kernel
theorem ranks157_linked : ReferenceRankData.CoarseLowerShape.Batch0019.targetR157=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0019.targetA157=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 1 := by decide +kernel
theorem r_input157_linked : ReferenceRankData.CoarseLowerShape.Batch0019.r157.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds.gauge] := by decide +kernel
theorem a_input157_linked : ReferenceRankData.CoarseLowerShape.Batch0019.a157.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.a157.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.a157.bounds.gauge] := by decide +kernel
theorem geometry157_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.a := by decide +kernel
theorem weights314_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0039.cert314.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights315_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0039.cert315.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time157_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 10)=true := by decide +kernel
theorem r_reference157_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 0)=true := by decide +kernel
theorem a_reference157_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 1)=true := by decide +kernel
theorem rank_r_link157_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r157 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link157_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0019.a157.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a157 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints157 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell true ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r157 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile157_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link157_checked
    geometry157_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell false ReferenceProfileData.CoarseLowerShape.Batch0019.a157.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a157 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile157_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link157_checked
    geometry157_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks157_linked.1,←ranks157_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0019.r157.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a157.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0019.ordered157_checked hr ha ho
theorem frozen_frame157 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157 ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds ReferenceProfileData.CoarseLowerShape.Batch0019.a157.bounds
  · rw [←r_profile157_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile157_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry157_linked.2.2.2.2.1
  · exact geometry157_linked.2.2.2.2.2
  · exact r_reference157_checked
  · exact a_reference157_checked
  · exact r_fixed157_linked
  · exact a_fixed157_linked
  · exact time157_checked
  · exact ht
  · exact hw
theorem child_geometry157_checked : ReferenceWeightData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights157 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0039.cert314∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch39_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0039.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0039.cert315∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch39_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0039.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0039.cert314.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry157_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights314_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0039.cert315.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry157_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry157_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights315_linked j (List.mem_finRange j))
theorem actual_frozen_frame157 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame157 (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.flow.timeParameter_mem child_geometry157_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights157 hz)
theorem r_profile158_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r158=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds := by rfl
theorem a_profile158_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a158=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a158.bounds := by rfl
theorem r_fixed158_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 7 := by decide +kernel
theorem a_fixed158_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a158.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.a158.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 9 := by decide +kernel
theorem ranks158_linked : ReferenceRankData.CoarseLowerShape.Batch0019.targetR158=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0019.targetA158=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 1 := by decide +kernel
theorem r_input158_linked : ReferenceRankData.CoarseLowerShape.Batch0019.r158.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds.gauge] := by decide +kernel
theorem a_input158_linked : ReferenceRankData.CoarseLowerShape.Batch0019.a158.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.a158.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.a158.bounds.gauge] := by decide +kernel
theorem geometry158_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.a := by decide +kernel
theorem weights316_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0039.cert316.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights317_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0039.cert317.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time158_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 10)=true := by decide +kernel
theorem r_reference158_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 0)=true := by decide +kernel
theorem a_reference158_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 1)=true := by decide +kernel
theorem rank_r_link158_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r158 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link158_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0019.a158.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a158 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints158 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell true ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r158 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile158_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link158_checked
    geometry158_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell false ReferenceProfileData.CoarseLowerShape.Batch0019.a158.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a158 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile158_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link158_checked
    geometry158_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks158_linked.1,←ranks158_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0019.r158.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a158.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0019.ordered158_checked hr ha ho
theorem frozen_frame158 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158 ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds ReferenceProfileData.CoarseLowerShape.Batch0019.a158.bounds
  · rw [←r_profile158_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile158_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry158_linked.2.2.2.2.1
  · exact geometry158_linked.2.2.2.2.2
  · exact r_reference158_checked
  · exact a_reference158_checked
  · exact r_fixed158_linked
  · exact a_fixed158_linked
  · exact time158_checked
  · exact ht
  · exact hw
theorem child_geometry158_checked : ReferenceWeightData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights158 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0039.cert316∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch39_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0039.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0039.cert317∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch39_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0039.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0039.cert316.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry158_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights316_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0039.cert317.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry158_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry158_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights317_linked j (List.mem_finRange j))
theorem actual_frozen_frame158 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame158 (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.flow.timeParameter_mem child_geometry158_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights158 hz)
theorem r_profile159_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r159=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds := by rfl
theorem a_profile159_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a159=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a159.bounds := by rfl
theorem r_fixed159_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 7 := by decide +kernel
theorem a_fixed159_linked : ReferenceProfileData.CoarseLowerShape.Batch0019.a159.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0019.a159.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 9 := by decide +kernel
theorem ranks159_linked : ReferenceRankData.CoarseLowerShape.Batch0019.targetR159=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0019.targetA159=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 1 := by decide +kernel
theorem r_input159_linked : ReferenceRankData.CoarseLowerShape.Batch0019.r159.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds.gauge] := by decide +kernel
theorem a_input159_linked : ReferenceRankData.CoarseLowerShape.Batch0019.a159.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0019.a159.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0019.a159.bounds.gauge] := by decide +kernel
theorem geometry159_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.a := by decide +kernel
theorem weights318_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0039.cert318.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights319_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0039.cert319.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time159_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 10)=true := by decide +kernel
theorem r_reference159_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 0)=true := by decide +kernel
theorem a_reference159_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 1)=true := by decide +kernel
theorem rank_r_link159_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r159 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link159_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0019.a159.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a159 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints159 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell true ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds ReferenceRankData.CoarseLowerShape.Batch0019.r159 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile159_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link159_checked
    geometry159_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell false ReferenceProfileData.CoarseLowerShape.Batch0019.a159.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a159 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile159_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0019.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0019.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link159_checked
    geometry159_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks159_linked.1,←ranks159_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0019.r159.bounds ReferenceRankData.CoarseLowerShape.Batch0019.a159.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0019.ordered159_checked hr ha ho
theorem frozen_frame159 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159 ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds ReferenceProfileData.CoarseLowerShape.Batch0019.a159.bounds
  · rw [←r_profile159_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile159_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry159_linked.2.2.2.2.1
  · exact geometry159_linked.2.2.2.2.2
  · exact r_reference159_checked
  · exact a_reference159_checked
  · exact r_fixed159_linked
  · exact a_fixed159_linked
  · exact time159_checked
  · exact ht
  · exact hw
theorem child_geometry159_checked : ReferenceWeightData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights159 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0039.cert318∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch39_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0039.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0039.cert319∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch39_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0039.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0039.cert318.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry159_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights318_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0039.cert319.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry159_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry159_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights319_linked j (List.mem_finRange j))
theorem actual_frozen_frame159 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame159 (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.flow.timeParameter_mem child_geometry159_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights159 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell152),(ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell153),(ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell154),(ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell155),(ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell156),(ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell157),(ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell158),(ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0019.cell159)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0019.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0019.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame152 hz
  · exact fun z hz=>actual_frozen_frame153 hz
  · exact fun z hz=>actual_frozen_frame154 hz
  · exact fun z hz=>actual_frozen_frame155 hz
  · exact fun z hz=>actual_frozen_frame156 hz
  · exact fun z hz=>actual_frozen_frame157 hz
  · exact fun z hz=>actual_frozen_frame158 hz
  · exact fun z hz=>actual_frozen_frame159 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints152 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints153 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints154 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints155 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints156 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints157 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints158 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints159 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry152_linked.1,geometry152_linked.2.1,geometry152_linked.2.2.1,geometry152_linked.2.2.2.1⟩
  · exact ⟨geometry153_linked.1,geometry153_linked.2.1,geometry153_linked.2.2.1,geometry153_linked.2.2.2.1⟩
  · exact ⟨geometry154_linked.1,geometry154_linked.2.1,geometry154_linked.2.2.1,geometry154_linked.2.2.2.1⟩
  · exact ⟨geometry155_linked.1,geometry155_linked.2.1,geometry155_linked.2.2.1,geometry155_linked.2.2.2.1⟩
  · exact ⟨geometry156_linked.1,geometry156_linked.2.1,geometry156_linked.2.2.1,geometry156_linked.2.2.2.1⟩
  · exact ⟨geometry157_linked.1,geometry157_linked.2.1,geometry157_linked.2.2.1,geometry157_linked.2.2.2.1⟩
  · exact ⟨geometry158_linked.1,geometry158_linked.2.1,geometry158_linked.2.2.1,geometry158_linked.2.2.2.1⟩
  · exact ⟨geometry159_linked.1,geometry159_linked.2.1,geometry159_linked.2.2.1,geometry159_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.a152.bounds,?_,geometry152_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a152.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile152_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds,?_,geometry152_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert152.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r152.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile152_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.a153.bounds,?_,geometry153_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a153.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile153_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds,?_,geometry153_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert153.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r153.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile153_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.a154.bounds,?_,geometry154_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a154.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile154_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds,?_,geometry154_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert154.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r154.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile154_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.a155.bounds,?_,geometry155_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a155.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile155_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds,?_,geometry155_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert155.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r155.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile155_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.a156.bounds,?_,geometry156_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a156.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile156_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds,?_,geometry156_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert156.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r156.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile156_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.a157.bounds,?_,geometry157_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a157.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile157_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds,?_,geometry157_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert157.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r157.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile157_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.a158.bounds,?_,geometry158_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a158.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile158_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds,?_,geometry158_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert158.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r158.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile158_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.a159.bounds,?_,geometry159_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0019.a159.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile159_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds,?_,geometry159_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0019.cert159.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0019.r159.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile159_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0019.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0019.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0019
