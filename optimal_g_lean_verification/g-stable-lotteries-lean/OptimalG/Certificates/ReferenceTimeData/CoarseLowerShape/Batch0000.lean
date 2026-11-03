import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Batch0000
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Batch0000
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0001_0004
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Batch0000
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Batch0000
namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch0_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0000.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch1_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0001.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile0_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r0=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds := by rfl
theorem a_profile0_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a0=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a0.bounds := by rfl
theorem r_fixed0_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 7 := by decide +kernel
theorem a_fixed0_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a0.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.a0.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 9 := by decide +kernel
theorem ranks0_linked : ReferenceRankData.CoarseLowerShape.Batch0000.targetR0=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0000.targetA0=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 1 := by decide +kernel
theorem r_input0_linked : ReferenceRankData.CoarseLowerShape.Batch0000.r0.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds.gauge] := by decide +kernel
theorem a_input0_linked : ReferenceRankData.CoarseLowerShape.Batch0000.a0.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.a0.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.a0.bounds.gauge] := by decide +kernel
theorem geometry0_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.a := by decide +kernel
theorem weights0_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights1_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time0_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 10)=true := by decide +kernel
theorem r_reference0_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 0)=true := by decide +kernel
theorem a_reference0_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 1)=true := by decide +kernel
theorem rank_r_link0_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r0 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link0_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0000.a0.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a0 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints0 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell true ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r0 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile0_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link0_checked
    geometry0_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell false ReferenceProfileData.CoarseLowerShape.Batch0000.a0.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a0 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile0_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link0_checked
    geometry0_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks0_linked.1,←ranks0_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0000.r0.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a0.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0000.ordered0_checked hr ha ho
theorem frozen_frame0 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0 ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds ReferenceProfileData.CoarseLowerShape.Batch0000.a0.bounds
  · rw [←r_profile0_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile0_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry0_linked.2.2.2.2.1
  · exact geometry0_linked.2.2.2.2.2
  · exact r_reference0_checked
  · exact a_reference0_checked
  · exact r_fixed0_linked
  · exact a_fixed0_linked
  · exact time0_checked
  · exact ht
  · exact hw
theorem child_geometry0_checked : ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights0 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0000.cert0∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch0_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0000.cert1∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch0_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry0_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights0_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry0_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry0_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights1_linked j (List.mem_finRange j))
theorem actual_frozen_frame0 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame0 (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.flow.timeParameter_mem child_geometry0_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights0 hz)
theorem r_profile1_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r1=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds := by rfl
theorem a_profile1_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a1=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a1.bounds := by rfl
theorem r_fixed1_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 7 := by decide +kernel
theorem a_fixed1_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a1.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.a1.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 9 := by decide +kernel
theorem ranks1_linked : ReferenceRankData.CoarseLowerShape.Batch0000.targetR1=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0000.targetA1=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 1 := by decide +kernel
theorem r_input1_linked : ReferenceRankData.CoarseLowerShape.Batch0000.r1.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds.gauge] := by decide +kernel
theorem a_input1_linked : ReferenceRankData.CoarseLowerShape.Batch0000.a1.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.a1.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.a1.bounds.gauge] := by decide +kernel
theorem geometry1_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.a := by decide +kernel
theorem weights2_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights3_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time1_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 10)=true := by decide +kernel
theorem r_reference1_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 0)=true := by decide +kernel
theorem a_reference1_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 1)=true := by decide +kernel
theorem rank_r_link1_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r1 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link1_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0000.a1.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a1 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints1 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell true ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r1 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile1_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link1_checked
    geometry1_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell false ReferenceProfileData.CoarseLowerShape.Batch0000.a1.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a1 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile1_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link1_checked
    geometry1_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks1_linked.1,←ranks1_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0000.r1.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a1.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0000.ordered1_checked hr ha ho
theorem frozen_frame1 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1 ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds ReferenceProfileData.CoarseLowerShape.Batch0000.a1.bounds
  · rw [←r_profile1_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile1_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry1_linked.2.2.2.2.1
  · exact geometry1_linked.2.2.2.2.2
  · exact r_reference1_checked
  · exact a_reference1_checked
  · exact r_fixed1_linked
  · exact a_fixed1_linked
  · exact time1_checked
  · exact ht
  · exact hw
theorem child_geometry1_checked : ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0000.cert2∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch0_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0000.cert3∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch0_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry1_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights2_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry1_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry1_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights3_linked j (List.mem_finRange j))
theorem actual_frozen_frame1 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame1 (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.flow.timeParameter_mem child_geometry1_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights1 hz)
theorem r_profile2_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r2=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds := by rfl
theorem a_profile2_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a2=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a2.bounds := by rfl
theorem r_fixed2_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 7 := by decide +kernel
theorem a_fixed2_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a2.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.a2.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 9 := by decide +kernel
theorem ranks2_linked : ReferenceRankData.CoarseLowerShape.Batch0000.targetR2=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0000.targetA2=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 1 := by decide +kernel
theorem r_input2_linked : ReferenceRankData.CoarseLowerShape.Batch0000.r2.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds.gauge] := by decide +kernel
theorem a_input2_linked : ReferenceRankData.CoarseLowerShape.Batch0000.a2.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.a2.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.a2.bounds.gauge] := by decide +kernel
theorem geometry2_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.a := by decide +kernel
theorem weights4_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights5_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time2_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 10)=true := by decide +kernel
theorem r_reference2_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 0)=true := by decide +kernel
theorem a_reference2_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 1)=true := by decide +kernel
theorem rank_r_link2_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r2 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link2_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0000.a2.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a2 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints2 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell true ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r2 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile2_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link2_checked
    geometry2_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell false ReferenceProfileData.CoarseLowerShape.Batch0000.a2.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a2 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile2_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link2_checked
    geometry2_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks2_linked.1,←ranks2_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0000.r2.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a2.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0000.ordered2_checked hr ha ho
theorem frozen_frame2 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2 ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds ReferenceProfileData.CoarseLowerShape.Batch0000.a2.bounds
  · rw [←r_profile2_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile2_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry2_linked.2.2.2.2.1
  · exact geometry2_linked.2.2.2.2.2
  · exact r_reference2_checked
  · exact a_reference2_checked
  · exact r_fixed2_linked
  · exact a_fixed2_linked
  · exact time2_checked
  · exact ht
  · exact hw
theorem child_geometry2_checked : ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0000.cert4∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch0_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0000.cert5∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch0_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry2_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights4_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry2_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry2_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights5_linked j (List.mem_finRange j))
theorem actual_frozen_frame2 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame2 (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.flow.timeParameter_mem child_geometry2_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights2 hz)
theorem r_profile3_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r3=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds := by rfl
theorem a_profile3_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a3=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a3.bounds := by rfl
theorem r_fixed3_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 7 := by decide +kernel
theorem a_fixed3_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a3.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.a3.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 9 := by decide +kernel
theorem ranks3_linked : ReferenceRankData.CoarseLowerShape.Batch0000.targetR3=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0000.targetA3=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 1 := by decide +kernel
theorem r_input3_linked : ReferenceRankData.CoarseLowerShape.Batch0000.r3.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds.gauge] := by decide +kernel
theorem a_input3_linked : ReferenceRankData.CoarseLowerShape.Batch0000.a3.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.a3.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.a3.bounds.gauge] := by decide +kernel
theorem geometry3_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.a := by decide +kernel
theorem weights6_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights7_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time3_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 10)=true := by decide +kernel
theorem r_reference3_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 0)=true := by decide +kernel
theorem a_reference3_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 1)=true := by decide +kernel
theorem rank_r_link3_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r3 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link3_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0000.a3.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a3 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints3 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell true ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r3 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile3_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link3_checked
    geometry3_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell false ReferenceProfileData.CoarseLowerShape.Batch0000.a3.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a3 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile3_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link3_checked
    geometry3_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks3_linked.1,←ranks3_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0000.r3.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a3.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0000.ordered3_checked hr ha ho
theorem frozen_frame3 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3 ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds ReferenceProfileData.CoarseLowerShape.Batch0000.a3.bounds
  · rw [←r_profile3_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile3_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry3_linked.2.2.2.2.1
  · exact geometry3_linked.2.2.2.2.2
  · exact r_reference3_checked
  · exact a_reference3_checked
  · exact r_fixed3_linked
  · exact a_fixed3_linked
  · exact time3_checked
  · exact ht
  · exact hw
theorem child_geometry3_checked : ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights3 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0000.cert6∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch0_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0000.cert7∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch0_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0000.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry3_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights6_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry3_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry3_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights7_linked j (List.mem_finRange j))
theorem actual_frozen_frame3 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame3 (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.flow.timeParameter_mem child_geometry3_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights3 hz)
theorem r_profile4_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r4=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds := by rfl
theorem a_profile4_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a4=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a4.bounds := by rfl
theorem r_fixed4_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 7 := by decide +kernel
theorem a_fixed4_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a4.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.a4.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 9 := by decide +kernel
theorem ranks4_linked : ReferenceRankData.CoarseLowerShape.Batch0000.targetR4=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0000.targetA4=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 1 := by decide +kernel
theorem r_input4_linked : ReferenceRankData.CoarseLowerShape.Batch0000.r4.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds.gauge] := by decide +kernel
theorem a_input4_linked : ReferenceRankData.CoarseLowerShape.Batch0000.a4.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.a4.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.a4.bounds.gauge] := by decide +kernel
theorem geometry4_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.a := by decide +kernel
theorem weights8_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights9_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time4_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 10)=true := by decide +kernel
theorem r_reference4_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 0)=true := by decide +kernel
theorem a_reference4_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 1)=true := by decide +kernel
theorem rank_r_link4_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r4 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link4_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0000.a4.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a4 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints4 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell true ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r4 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile4_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link4_checked
    geometry4_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell false ReferenceProfileData.CoarseLowerShape.Batch0000.a4.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a4 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile4_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link4_checked
    geometry4_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks4_linked.1,←ranks4_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0000.r4.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a4.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0000.ordered4_checked hr ha ho
theorem frozen_frame4 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4 ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds ReferenceProfileData.CoarseLowerShape.Batch0000.a4.bounds
  · rw [←r_profile4_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile4_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry4_linked.2.2.2.2.1
  · exact geometry4_linked.2.2.2.2.2
  · exact r_reference4_checked
  · exact a_reference4_checked
  · exact r_fixed4_linked
  · exact a_fixed4_linked
  · exact time4_checked
  · exact ht
  · exact hw
theorem child_geometry4_checked : ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights4 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0001.cert8∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch1_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0001.cert9∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch1_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry4_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights8_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry4_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry4_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights9_linked j (List.mem_finRange j))
theorem actual_frozen_frame4 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame4 (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.flow.timeParameter_mem child_geometry4_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights4 hz)
theorem r_profile5_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r5=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds := by rfl
theorem a_profile5_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a5=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a5.bounds := by rfl
theorem r_fixed5_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 7 := by decide +kernel
theorem a_fixed5_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a5.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.a5.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 9 := by decide +kernel
theorem ranks5_linked : ReferenceRankData.CoarseLowerShape.Batch0000.targetR5=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0000.targetA5=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 1 := by decide +kernel
theorem r_input5_linked : ReferenceRankData.CoarseLowerShape.Batch0000.r5.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds.gauge] := by decide +kernel
theorem a_input5_linked : ReferenceRankData.CoarseLowerShape.Batch0000.a5.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.a5.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.a5.bounds.gauge] := by decide +kernel
theorem geometry5_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.a := by decide +kernel
theorem weights10_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights11_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time5_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 10)=true := by decide +kernel
theorem r_reference5_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 0)=true := by decide +kernel
theorem a_reference5_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 1)=true := by decide +kernel
theorem rank_r_link5_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r5 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link5_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0000.a5.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a5 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints5 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell true ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r5 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile5_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link5_checked
    geometry5_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell false ReferenceProfileData.CoarseLowerShape.Batch0000.a5.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a5 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile5_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link5_checked
    geometry5_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks5_linked.1,←ranks5_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0000.r5.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a5.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0000.ordered5_checked hr ha ho
theorem frozen_frame5 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5 ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds ReferenceProfileData.CoarseLowerShape.Batch0000.a5.bounds
  · rw [←r_profile5_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile5_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry5_linked.2.2.2.2.1
  · exact geometry5_linked.2.2.2.2.2
  · exact r_reference5_checked
  · exact a_reference5_checked
  · exact r_fixed5_linked
  · exact a_fixed5_linked
  · exact time5_checked
  · exact ht
  · exact hw
theorem child_geometry5_checked : ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights5 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0001.cert10∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch1_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0001.cert11∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch1_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry5_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights10_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry5_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry5_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights11_linked j (List.mem_finRange j))
theorem actual_frozen_frame5 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame5 (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.flow.timeParameter_mem child_geometry5_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights5 hz)
theorem r_profile6_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r6=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds := by rfl
theorem a_profile6_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a6=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a6.bounds := by rfl
theorem r_fixed6_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 7 := by decide +kernel
theorem a_fixed6_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a6.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.a6.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 9 := by decide +kernel
theorem ranks6_linked : ReferenceRankData.CoarseLowerShape.Batch0000.targetR6=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0000.targetA6=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 1 := by decide +kernel
theorem r_input6_linked : ReferenceRankData.CoarseLowerShape.Batch0000.r6.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds.gauge] := by decide +kernel
theorem a_input6_linked : ReferenceRankData.CoarseLowerShape.Batch0000.a6.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.a6.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.a6.bounds.gauge] := by decide +kernel
theorem geometry6_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.a := by decide +kernel
theorem weights12_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights13_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time6_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 10)=true := by decide +kernel
theorem r_reference6_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 0)=true := by decide +kernel
theorem a_reference6_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 1)=true := by decide +kernel
theorem rank_r_link6_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r6 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link6_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0000.a6.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a6 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints6 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell true ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r6 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile6_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link6_checked
    geometry6_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell false ReferenceProfileData.CoarseLowerShape.Batch0000.a6.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a6 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile6_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link6_checked
    geometry6_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks6_linked.1,←ranks6_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0000.r6.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a6.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0000.ordered6_checked hr ha ho
theorem frozen_frame6 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6 ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds ReferenceProfileData.CoarseLowerShape.Batch0000.a6.bounds
  · rw [←r_profile6_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile6_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry6_linked.2.2.2.2.1
  · exact geometry6_linked.2.2.2.2.2
  · exact r_reference6_checked
  · exact a_reference6_checked
  · exact r_fixed6_linked
  · exact a_fixed6_linked
  · exact time6_checked
  · exact ht
  · exact hw
theorem child_geometry6_checked : ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights6 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0001.cert12∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch1_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0001.cert13∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch1_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry6_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights12_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry6_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry6_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights13_linked j (List.mem_finRange j))
theorem actual_frozen_frame6 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame6 (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.flow.timeParameter_mem child_geometry6_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights6 hz)
theorem r_profile7_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r7=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds := by rfl
theorem a_profile7_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a7=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a7.bounds := by rfl
theorem r_fixed7_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 7 := by decide +kernel
theorem a_fixed7_linked : ReferenceProfileData.CoarseLowerShape.Batch0000.a7.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0000.a7.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 9 := by decide +kernel
theorem ranks7_linked : ReferenceRankData.CoarseLowerShape.Batch0000.targetR7=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0000.targetA7=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 1 := by decide +kernel
theorem r_input7_linked : ReferenceRankData.CoarseLowerShape.Batch0000.r7.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds.gauge] := by decide +kernel
theorem a_input7_linked : ReferenceRankData.CoarseLowerShape.Batch0000.a7.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0000.a7.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0000.a7.bounds.gauge] := by decide +kernel
theorem geometry7_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.a := by decide +kernel
theorem weights14_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights15_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time7_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 10)=true := by decide +kernel
theorem r_reference7_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 0)=true := by decide +kernel
theorem a_reference7_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 1)=true := by decide +kernel
theorem rank_r_link7_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r7 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link7_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0000.a7.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a7 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints7 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell true ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds ReferenceRankData.CoarseLowerShape.Batch0000.r7 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile7_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link7_checked
    geometry7_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell false ReferenceProfileData.CoarseLowerShape.Batch0000.a7.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a7 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile7_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0000.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0000.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link7_checked
    geometry7_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks7_linked.1,←ranks7_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0000.r7.bounds ReferenceRankData.CoarseLowerShape.Batch0000.a7.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0000.ordered7_checked hr ha ho
theorem frozen_frame7 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7 ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds ReferenceProfileData.CoarseLowerShape.Batch0000.a7.bounds
  · rw [←r_profile7_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile7_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry7_linked.2.2.2.2.1
  · exact geometry7_linked.2.2.2.2.2
  · exact r_reference7_checked
  · exact a_reference7_checked
  · exact r_fixed7_linked
  · exact a_fixed7_linked
  · exact time7_checked
  · exact ht
  · exact hw
theorem child_geometry7_checked : ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights7 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0001.cert14∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch1_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0001.cert15∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch1_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0001.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry7_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights14_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry7_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry7_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights15_linked j (List.mem_finRange j))
theorem actual_frozen_frame7 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame7 (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.flow.timeParameter_mem child_geometry7_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights7 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell0),(ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell1),(ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell2),(ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell3),(ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell4),(ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell5),(ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell6),(ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0000.cell7)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0000.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0000.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame0 hz
  · exact fun z hz=>actual_frozen_frame1 hz
  · exact fun z hz=>actual_frozen_frame2 hz
  · exact fun z hz=>actual_frozen_frame3 hz
  · exact fun z hz=>actual_frozen_frame4 hz
  · exact fun z hz=>actual_frozen_frame5 hz
  · exact fun z hz=>actual_frozen_frame6 hz
  · exact fun z hz=>actual_frozen_frame7 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints0 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints1 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints2 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints3 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints4 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints5 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints6 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints7 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry0_linked.1,geometry0_linked.2.1,geometry0_linked.2.2.1,geometry0_linked.2.2.2.1⟩
  · exact ⟨geometry1_linked.1,geometry1_linked.2.1,geometry1_linked.2.2.1,geometry1_linked.2.2.2.1⟩
  · exact ⟨geometry2_linked.1,geometry2_linked.2.1,geometry2_linked.2.2.1,geometry2_linked.2.2.2.1⟩
  · exact ⟨geometry3_linked.1,geometry3_linked.2.1,geometry3_linked.2.2.1,geometry3_linked.2.2.2.1⟩
  · exact ⟨geometry4_linked.1,geometry4_linked.2.1,geometry4_linked.2.2.1,geometry4_linked.2.2.2.1⟩
  · exact ⟨geometry5_linked.1,geometry5_linked.2.1,geometry5_linked.2.2.1,geometry5_linked.2.2.2.1⟩
  · exact ⟨geometry6_linked.1,geometry6_linked.2.1,geometry6_linked.2.2.1,geometry6_linked.2.2.2.1⟩
  · exact ⟨geometry7_linked.1,geometry7_linked.2.1,geometry7_linked.2.2.1,geometry7_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.a0.bounds,?_,geometry0_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a0.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile0_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds,?_,geometry0_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert0.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r0.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile0_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.a1.bounds,?_,geometry1_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a1.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile1_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds,?_,geometry1_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert1.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r1.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile1_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.a2.bounds,?_,geometry2_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a2.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile2_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds,?_,geometry2_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert2.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r2.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile2_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.a3.bounds,?_,geometry3_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a3.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile3_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds,?_,geometry3_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert3.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r3.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile3_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.a4.bounds,?_,geometry4_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a4.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile4_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds,?_,geometry4_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert4.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r4.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile4_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.a5.bounds,?_,geometry5_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a5.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile5_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds,?_,geometry5_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert5.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r5.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile5_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.a6.bounds,?_,geometry6_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a6.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile6_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds,?_,geometry6_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert6.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r6.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile6_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.a7.bounds,?_,geometry7_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0000.a7.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile7_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds,?_,geometry7_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0000.cert7.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0000.r7.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile7_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0000.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0000.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0000
