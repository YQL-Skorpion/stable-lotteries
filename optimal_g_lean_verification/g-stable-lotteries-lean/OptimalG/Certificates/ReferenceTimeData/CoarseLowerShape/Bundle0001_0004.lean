import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0001_0004
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0001_0004
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0001_0004
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Batch0001
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Batch0001
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0000
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0005_0008
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Batch0002
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Batch0002
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Batch0003
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0003_0006
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0009_0012
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Batch0004

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0001
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch2_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0002.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch3_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0003.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile8_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r8=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds := by rfl
theorem a_profile8_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a8=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a8.bounds := by rfl
theorem r_fixed8_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 7 := by decide +kernel
theorem a_fixed8_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a8.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.a8.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 9 := by decide +kernel
theorem ranks8_linked : ReferenceRankData.CoarseLowerShape.Batch0001.targetR8=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0001.targetA8=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 1 := by decide +kernel
theorem r_input8_linked : ReferenceRankData.CoarseLowerShape.Batch0001.r8.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds.gauge] := by decide +kernel
theorem a_input8_linked : ReferenceRankData.CoarseLowerShape.Batch0001.a8.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.a8.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.a8.bounds.gauge] := by decide +kernel
theorem geometry8_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.a := by decide +kernel
theorem weights16_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights17_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time8_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 10)=true := by decide +kernel
theorem r_reference8_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 0)=true := by decide +kernel
theorem a_reference8_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 1)=true := by decide +kernel
theorem rank_r_link8_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r8 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link8_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0001.a8.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a8 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints8 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell true ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r8 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile8_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link8_checked
    geometry8_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell false ReferenceProfileData.CoarseLowerShape.Batch0001.a8.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a8 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile8_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link8_checked
    geometry8_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks8_linked.1,←ranks8_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0001.r8.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a8.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0001.ordered8_checked hr ha ho
theorem frozen_frame8 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8 ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds ReferenceProfileData.CoarseLowerShape.Batch0001.a8.bounds
  · rw [←r_profile8_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile8_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry8_linked.2.2.2.2.1
  · exact geometry8_linked.2.2.2.2.2
  · exact r_reference8_checked
  · exact a_reference8_checked
  · exact r_fixed8_linked
  · exact a_fixed8_linked
  · exact time8_checked
  · exact ht
  · exact hw
theorem child_geometry8_checked : ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights8 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0002.cert16∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch2_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0002.cert17∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch2_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry8_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights16_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry8_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry8_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights17_linked j (List.mem_finRange j))
theorem actual_frozen_frame8 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame8 (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.flow.timeParameter_mem child_geometry8_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights8 hz)
theorem r_profile9_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r9=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds := by rfl
theorem a_profile9_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a9=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a9.bounds := by rfl
theorem r_fixed9_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 7 := by decide +kernel
theorem a_fixed9_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a9.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.a9.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 9 := by decide +kernel
theorem ranks9_linked : ReferenceRankData.CoarseLowerShape.Batch0001.targetR9=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0001.targetA9=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 1 := by decide +kernel
theorem r_input9_linked : ReferenceRankData.CoarseLowerShape.Batch0001.r9.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds.gauge] := by decide +kernel
theorem a_input9_linked : ReferenceRankData.CoarseLowerShape.Batch0001.a9.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.a9.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.a9.bounds.gauge] := by decide +kernel
theorem geometry9_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.a := by decide +kernel
theorem weights18_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights19_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time9_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 10)=true := by decide +kernel
theorem r_reference9_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 0)=true := by decide +kernel
theorem a_reference9_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 1)=true := by decide +kernel
theorem rank_r_link9_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r9 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link9_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0001.a9.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a9 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints9 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell true ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r9 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile9_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link9_checked
    geometry9_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell false ReferenceProfileData.CoarseLowerShape.Batch0001.a9.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a9 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile9_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link9_checked
    geometry9_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks9_linked.1,←ranks9_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0001.r9.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a9.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0001.ordered9_checked hr ha ho
theorem frozen_frame9 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9 ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds ReferenceProfileData.CoarseLowerShape.Batch0001.a9.bounds
  · rw [←r_profile9_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile9_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry9_linked.2.2.2.2.1
  · exact geometry9_linked.2.2.2.2.2
  · exact r_reference9_checked
  · exact a_reference9_checked
  · exact r_fixed9_linked
  · exact a_fixed9_linked
  · exact time9_checked
  · exact ht
  · exact hw
theorem child_geometry9_checked : ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights9 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0002.cert18∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch2_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0002.cert19∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch2_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry9_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights18_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry9_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry9_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights19_linked j (List.mem_finRange j))
theorem actual_frozen_frame9 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame9 (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.flow.timeParameter_mem child_geometry9_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights9 hz)
theorem r_profile10_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r10=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds := by rfl
theorem a_profile10_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a10=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a10.bounds := by rfl
theorem r_fixed10_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 7 := by decide +kernel
theorem a_fixed10_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a10.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.a10.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 9 := by decide +kernel
theorem ranks10_linked : ReferenceRankData.CoarseLowerShape.Batch0001.targetR10=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0001.targetA10=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 1 := by decide +kernel
theorem r_input10_linked : ReferenceRankData.CoarseLowerShape.Batch0001.r10.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds.gauge] := by decide +kernel
theorem a_input10_linked : ReferenceRankData.CoarseLowerShape.Batch0001.a10.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.a10.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.a10.bounds.gauge] := by decide +kernel
theorem geometry10_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.a := by decide +kernel
theorem weights20_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights21_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time10_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 10)=true := by decide +kernel
theorem r_reference10_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 0)=true := by decide +kernel
theorem a_reference10_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 1)=true := by decide +kernel
theorem rank_r_link10_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r10 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link10_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0001.a10.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a10 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints10 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell true ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r10 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile10_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link10_checked
    geometry10_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell false ReferenceProfileData.CoarseLowerShape.Batch0001.a10.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a10 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile10_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link10_checked
    geometry10_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks10_linked.1,←ranks10_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0001.r10.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a10.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0001.ordered10_checked hr ha ho
theorem frozen_frame10 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10 ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds ReferenceProfileData.CoarseLowerShape.Batch0001.a10.bounds
  · rw [←r_profile10_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile10_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry10_linked.2.2.2.2.1
  · exact geometry10_linked.2.2.2.2.2
  · exact r_reference10_checked
  · exact a_reference10_checked
  · exact r_fixed10_linked
  · exact a_fixed10_linked
  · exact time10_checked
  · exact ht
  · exact hw
theorem child_geometry10_checked : ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights10 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0002.cert20∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch2_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0002.cert21∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch2_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry10_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights20_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry10_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry10_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights21_linked j (List.mem_finRange j))
theorem actual_frozen_frame10 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame10 (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.flow.timeParameter_mem child_geometry10_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights10 hz)
theorem r_profile11_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r11=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds := by rfl
theorem a_profile11_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a11=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a11.bounds := by rfl
theorem r_fixed11_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 7 := by decide +kernel
theorem a_fixed11_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a11.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.a11.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 9 := by decide +kernel
theorem ranks11_linked : ReferenceRankData.CoarseLowerShape.Batch0001.targetR11=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0001.targetA11=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 1 := by decide +kernel
theorem r_input11_linked : ReferenceRankData.CoarseLowerShape.Batch0001.r11.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds.gauge] := by decide +kernel
theorem a_input11_linked : ReferenceRankData.CoarseLowerShape.Batch0001.a11.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.a11.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.a11.bounds.gauge] := by decide +kernel
theorem geometry11_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.a := by decide +kernel
theorem weights22_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights23_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time11_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 10)=true := by decide +kernel
theorem r_reference11_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 0)=true := by decide +kernel
theorem a_reference11_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 1)=true := by decide +kernel
theorem rank_r_link11_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r11 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link11_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0001.a11.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a11 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints11 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell true ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r11 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile11_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link11_checked
    geometry11_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell false ReferenceProfileData.CoarseLowerShape.Batch0001.a11.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a11 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile11_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link11_checked
    geometry11_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks11_linked.1,←ranks11_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0001.r11.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a11.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0001.ordered11_checked hr ha ho
theorem frozen_frame11 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11 ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds ReferenceProfileData.CoarseLowerShape.Batch0001.a11.bounds
  · rw [←r_profile11_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile11_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry11_linked.2.2.2.2.1
  · exact geometry11_linked.2.2.2.2.2
  · exact r_reference11_checked
  · exact a_reference11_checked
  · exact r_fixed11_linked
  · exact a_fixed11_linked
  · exact time11_checked
  · exact ht
  · exact hw
theorem child_geometry11_checked : ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights11 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0002.cert22∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch2_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0002.cert23∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch2_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0002.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry11_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights22_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry11_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry11_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights23_linked j (List.mem_finRange j))
theorem actual_frozen_frame11 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame11 (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.flow.timeParameter_mem child_geometry11_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights11 hz)
theorem r_profile12_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r12=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds := by rfl
theorem a_profile12_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a12=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a12.bounds := by rfl
theorem r_fixed12_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 7 := by decide +kernel
theorem a_fixed12_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a12.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.a12.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 9 := by decide +kernel
theorem ranks12_linked : ReferenceRankData.CoarseLowerShape.Batch0001.targetR12=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0001.targetA12=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 1 := by decide +kernel
theorem r_input12_linked : ReferenceRankData.CoarseLowerShape.Batch0001.r12.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds.gauge] := by decide +kernel
theorem a_input12_linked : ReferenceRankData.CoarseLowerShape.Batch0001.a12.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.a12.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.a12.bounds.gauge] := by decide +kernel
theorem geometry12_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.a := by decide +kernel
theorem weights24_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights25_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time12_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 10)=true := by decide +kernel
theorem r_reference12_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 0)=true := by decide +kernel
theorem a_reference12_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 1)=true := by decide +kernel
theorem rank_r_link12_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r12 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link12_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0001.a12.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a12 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints12 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell true ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r12 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile12_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link12_checked
    geometry12_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell false ReferenceProfileData.CoarseLowerShape.Batch0001.a12.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a12 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile12_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link12_checked
    geometry12_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks12_linked.1,←ranks12_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0001.r12.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a12.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0001.ordered12_checked hr ha ho
theorem frozen_frame12 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12 ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds ReferenceProfileData.CoarseLowerShape.Batch0001.a12.bounds
  · rw [←r_profile12_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile12_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry12_linked.2.2.2.2.1
  · exact geometry12_linked.2.2.2.2.2
  · exact r_reference12_checked
  · exact a_reference12_checked
  · exact r_fixed12_linked
  · exact a_fixed12_linked
  · exact time12_checked
  · exact ht
  · exact hw
theorem child_geometry12_checked : ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights12 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0003.cert24∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch3_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0003.cert25∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch3_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry12_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights24_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry12_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry12_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights25_linked j (List.mem_finRange j))
theorem actual_frozen_frame12 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame12 (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.flow.timeParameter_mem child_geometry12_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights12 hz)
theorem r_profile13_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r13=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds := by rfl
theorem a_profile13_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a13=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a13.bounds := by rfl
theorem r_fixed13_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 7 := by decide +kernel
theorem a_fixed13_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a13.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.a13.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 9 := by decide +kernel
theorem ranks13_linked : ReferenceRankData.CoarseLowerShape.Batch0001.targetR13=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0001.targetA13=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 1 := by decide +kernel
theorem r_input13_linked : ReferenceRankData.CoarseLowerShape.Batch0001.r13.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds.gauge] := by decide +kernel
theorem a_input13_linked : ReferenceRankData.CoarseLowerShape.Batch0001.a13.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.a13.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.a13.bounds.gauge] := by decide +kernel
theorem geometry13_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.a := by decide +kernel
theorem weights26_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights27_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time13_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 10)=true := by decide +kernel
theorem r_reference13_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 0)=true := by decide +kernel
theorem a_reference13_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 1)=true := by decide +kernel
theorem rank_r_link13_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r13 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link13_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0001.a13.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a13 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints13 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell true ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r13 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile13_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link13_checked
    geometry13_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell false ReferenceProfileData.CoarseLowerShape.Batch0001.a13.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a13 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile13_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link13_checked
    geometry13_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks13_linked.1,←ranks13_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0001.r13.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a13.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0001.ordered13_checked hr ha ho
theorem frozen_frame13 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13 ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds ReferenceProfileData.CoarseLowerShape.Batch0001.a13.bounds
  · rw [←r_profile13_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile13_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry13_linked.2.2.2.2.1
  · exact geometry13_linked.2.2.2.2.2
  · exact r_reference13_checked
  · exact a_reference13_checked
  · exact r_fixed13_linked
  · exact a_fixed13_linked
  · exact time13_checked
  · exact ht
  · exact hw
theorem child_geometry13_checked : ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights13 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0003.cert26∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch3_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0003.cert27∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch3_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry13_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights26_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry13_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry13_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights27_linked j (List.mem_finRange j))
theorem actual_frozen_frame13 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame13 (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.flow.timeParameter_mem child_geometry13_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights13 hz)
theorem r_profile14_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r14=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds := by rfl
theorem a_profile14_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a14=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a14.bounds := by rfl
theorem r_fixed14_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 7 := by decide +kernel
theorem a_fixed14_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a14.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.a14.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 9 := by decide +kernel
theorem ranks14_linked : ReferenceRankData.CoarseLowerShape.Batch0001.targetR14=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0001.targetA14=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 1 := by decide +kernel
theorem r_input14_linked : ReferenceRankData.CoarseLowerShape.Batch0001.r14.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds.gauge] := by decide +kernel
theorem a_input14_linked : ReferenceRankData.CoarseLowerShape.Batch0001.a14.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.a14.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.a14.bounds.gauge] := by decide +kernel
theorem geometry14_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.a := by decide +kernel
theorem weights28_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights29_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time14_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 10)=true := by decide +kernel
theorem r_reference14_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 0)=true := by decide +kernel
theorem a_reference14_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 1)=true := by decide +kernel
theorem rank_r_link14_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r14 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link14_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0001.a14.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a14 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints14 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell true ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r14 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile14_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link14_checked
    geometry14_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell false ReferenceProfileData.CoarseLowerShape.Batch0001.a14.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a14 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile14_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link14_checked
    geometry14_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks14_linked.1,←ranks14_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0001.r14.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a14.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0001.ordered14_checked hr ha ho
theorem frozen_frame14 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14 ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds ReferenceProfileData.CoarseLowerShape.Batch0001.a14.bounds
  · rw [←r_profile14_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile14_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry14_linked.2.2.2.2.1
  · exact geometry14_linked.2.2.2.2.2
  · exact r_reference14_checked
  · exact a_reference14_checked
  · exact r_fixed14_linked
  · exact a_fixed14_linked
  · exact time14_checked
  · exact ht
  · exact hw
theorem child_geometry14_checked : ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights14 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0003.cert28∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch3_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0003.cert29∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch3_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry14_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights28_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry14_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry14_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights29_linked j (List.mem_finRange j))
theorem actual_frozen_frame14 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame14 (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.flow.timeParameter_mem child_geometry14_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights14 hz)
theorem r_profile15_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r15=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds := by rfl
theorem a_profile15_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a15=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a15.bounds := by rfl
theorem r_fixed15_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 7 := by decide +kernel
theorem a_fixed15_linked : ReferenceProfileData.CoarseLowerShape.Batch0001.a15.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0001.a15.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 9 := by decide +kernel
theorem ranks15_linked : ReferenceRankData.CoarseLowerShape.Batch0001.targetR15=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0001.targetA15=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 1 := by decide +kernel
theorem r_input15_linked : ReferenceRankData.CoarseLowerShape.Batch0001.r15.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds.gauge] := by decide +kernel
theorem a_input15_linked : ReferenceRankData.CoarseLowerShape.Batch0001.a15.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0001.a15.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0001.a15.bounds.gauge] := by decide +kernel
theorem geometry15_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.a := by decide +kernel
theorem weights30_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights31_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time15_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 10)=true := by decide +kernel
theorem r_reference15_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 0)=true := by decide +kernel
theorem a_reference15_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 1)=true := by decide +kernel
theorem rank_r_link15_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r15 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link15_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0001.a15.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a15 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints15 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell true ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds ReferenceRankData.CoarseLowerShape.Batch0001.r15 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile15_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link15_checked
    geometry15_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell false ReferenceProfileData.CoarseLowerShape.Batch0001.a15.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a15 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile15_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0001.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0001.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link15_checked
    geometry15_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks15_linked.1,←ranks15_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0001.r15.bounds ReferenceRankData.CoarseLowerShape.Batch0001.a15.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0001.ordered15_checked hr ha ho
theorem frozen_frame15 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15 ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds ReferenceProfileData.CoarseLowerShape.Batch0001.a15.bounds
  · rw [←r_profile15_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile15_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry15_linked.2.2.2.2.1
  · exact geometry15_linked.2.2.2.2.2
  · exact r_reference15_checked
  · exact a_reference15_checked
  · exact r_fixed15_linked
  · exact a_fixed15_linked
  · exact time15_checked
  · exact ht
  · exact hw
theorem child_geometry15_checked : ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights15 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0003.cert30∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch3_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0003.cert31∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch3_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0003.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry15_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights30_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry15_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry15_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights31_linked j (List.mem_finRange j))
theorem actual_frozen_frame15 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame15 (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.flow.timeParameter_mem child_geometry15_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights15 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell8),(ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell9),(ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell10),(ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell11),(ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell12),(ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell13),(ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell14),(ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0001.cell15)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0001.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0001.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame8 hz
  · exact fun z hz=>actual_frozen_frame9 hz
  · exact fun z hz=>actual_frozen_frame10 hz
  · exact fun z hz=>actual_frozen_frame11 hz
  · exact fun z hz=>actual_frozen_frame12 hz
  · exact fun z hz=>actual_frozen_frame13 hz
  · exact fun z hz=>actual_frozen_frame14 hz
  · exact fun z hz=>actual_frozen_frame15 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints8 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints9 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints10 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints11 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints12 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints13 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints14 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints15 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry8_linked.1,geometry8_linked.2.1,geometry8_linked.2.2.1,geometry8_linked.2.2.2.1⟩
  · exact ⟨geometry9_linked.1,geometry9_linked.2.1,geometry9_linked.2.2.1,geometry9_linked.2.2.2.1⟩
  · exact ⟨geometry10_linked.1,geometry10_linked.2.1,geometry10_linked.2.2.1,geometry10_linked.2.2.2.1⟩
  · exact ⟨geometry11_linked.1,geometry11_linked.2.1,geometry11_linked.2.2.1,geometry11_linked.2.2.2.1⟩
  · exact ⟨geometry12_linked.1,geometry12_linked.2.1,geometry12_linked.2.2.1,geometry12_linked.2.2.2.1⟩
  · exact ⟨geometry13_linked.1,geometry13_linked.2.1,geometry13_linked.2.2.1,geometry13_linked.2.2.2.1⟩
  · exact ⟨geometry14_linked.1,geometry14_linked.2.1,geometry14_linked.2.2.1,geometry14_linked.2.2.2.1⟩
  · exact ⟨geometry15_linked.1,geometry15_linked.2.1,geometry15_linked.2.2.1,geometry15_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.a8.bounds,?_,geometry8_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a8.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile8_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds,?_,geometry8_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert8.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r8.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile8_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.a9.bounds,?_,geometry9_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a9.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile9_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds,?_,geometry9_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert9.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r9.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile9_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.a10.bounds,?_,geometry10_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a10.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile10_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds,?_,geometry10_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert10.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r10.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile10_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.a11.bounds,?_,geometry11_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a11.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile11_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds,?_,geometry11_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert11.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r11.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile11_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.a12.bounds,?_,geometry12_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a12.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile12_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds,?_,geometry12_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert12.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r12.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile12_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.a13.bounds,?_,geometry13_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a13.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile13_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds,?_,geometry13_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert13.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r13.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile13_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.a14.bounds,?_,geometry14_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a14.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile14_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds,?_,geometry14_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert14.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r14.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile14_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.a15.bounds,?_,geometry15_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0001.a15.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile15_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds,?_,geometry15_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0001.cert15.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0001.r15.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile15_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0001.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0001.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0001

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0002
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch4_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0004.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch5_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0005.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0005.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile16_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r16=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds := by rfl
theorem a_profile16_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a16=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a16.bounds := by rfl
theorem r_fixed16_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 7 := by decide +kernel
theorem a_fixed16_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a16.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.a16.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 9 := by decide +kernel
theorem ranks16_linked : ReferenceRankData.CoarseLowerShape.Batch0002.targetR16=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0002.targetA16=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 1 := by decide +kernel
theorem r_input16_linked : ReferenceRankData.CoarseLowerShape.Batch0002.r16.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds.gauge] := by decide +kernel
theorem a_input16_linked : ReferenceRankData.CoarseLowerShape.Batch0002.a16.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.a16.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.a16.bounds.gauge] := by decide +kernel
theorem geometry16_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.a := by decide +kernel
theorem weights32_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights33_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time16_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 10)=true := by decide +kernel
theorem r_reference16_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 0)=true := by decide +kernel
theorem a_reference16_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 1)=true := by decide +kernel
theorem rank_r_link16_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r16 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link16_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0002.a16.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a16 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints16 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell true ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r16 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile16_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link16_checked
    geometry16_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell false ReferenceProfileData.CoarseLowerShape.Batch0002.a16.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a16 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile16_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link16_checked
    geometry16_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks16_linked.1,←ranks16_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0002.r16.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a16.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0002.ordered16_checked hr ha ho
theorem frozen_frame16 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16 ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds ReferenceProfileData.CoarseLowerShape.Batch0002.a16.bounds
  · rw [←r_profile16_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile16_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry16_linked.2.2.2.2.1
  · exact geometry16_linked.2.2.2.2.2
  · exact r_reference16_checked
  · exact a_reference16_checked
  · exact r_fixed16_linked
  · exact a_fixed16_linked
  · exact time16_checked
  · exact ht
  · exact hw
theorem child_geometry16_checked : ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights16 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0004.cert32∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch4_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0004.cert33∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch4_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry16_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights32_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry16_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry16_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights33_linked j (List.mem_finRange j))
theorem actual_frozen_frame16 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame16 (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.flow.timeParameter_mem child_geometry16_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights16 hz)
theorem r_profile17_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r17=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds := by rfl
theorem a_profile17_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a17=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a17.bounds := by rfl
theorem r_fixed17_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 7 := by decide +kernel
theorem a_fixed17_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a17.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.a17.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 9 := by decide +kernel
theorem ranks17_linked : ReferenceRankData.CoarseLowerShape.Batch0002.targetR17=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0002.targetA17=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 1 := by decide +kernel
theorem r_input17_linked : ReferenceRankData.CoarseLowerShape.Batch0002.r17.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds.gauge] := by decide +kernel
theorem a_input17_linked : ReferenceRankData.CoarseLowerShape.Batch0002.a17.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.a17.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.a17.bounds.gauge] := by decide +kernel
theorem geometry17_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.a := by decide +kernel
theorem weights34_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights35_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time17_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 10)=true := by decide +kernel
theorem r_reference17_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 0)=true := by decide +kernel
theorem a_reference17_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 1)=true := by decide +kernel
theorem rank_r_link17_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r17 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link17_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0002.a17.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a17 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints17 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell true ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r17 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile17_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link17_checked
    geometry17_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell false ReferenceProfileData.CoarseLowerShape.Batch0002.a17.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a17 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile17_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link17_checked
    geometry17_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks17_linked.1,←ranks17_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0002.r17.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a17.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0002.ordered17_checked hr ha ho
theorem frozen_frame17 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17 ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds ReferenceProfileData.CoarseLowerShape.Batch0002.a17.bounds
  · rw [←r_profile17_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile17_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry17_linked.2.2.2.2.1
  · exact geometry17_linked.2.2.2.2.2
  · exact r_reference17_checked
  · exact a_reference17_checked
  · exact r_fixed17_linked
  · exact a_fixed17_linked
  · exact time17_checked
  · exact ht
  · exact hw
theorem child_geometry17_checked : ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights17 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0004.cert34∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch4_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0004.cert35∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch4_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry17_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights34_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry17_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry17_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights35_linked j (List.mem_finRange j))
theorem actual_frozen_frame17 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame17 (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.flow.timeParameter_mem child_geometry17_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights17 hz)
theorem r_profile18_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r18=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds := by rfl
theorem a_profile18_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a18=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a18.bounds := by rfl
theorem r_fixed18_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 7 := by decide +kernel
theorem a_fixed18_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a18.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.a18.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 9 := by decide +kernel
theorem ranks18_linked : ReferenceRankData.CoarseLowerShape.Batch0002.targetR18=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0002.targetA18=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 1 := by decide +kernel
theorem r_input18_linked : ReferenceRankData.CoarseLowerShape.Batch0002.r18.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds.gauge] := by decide +kernel
theorem a_input18_linked : ReferenceRankData.CoarseLowerShape.Batch0002.a18.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.a18.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.a18.bounds.gauge] := by decide +kernel
theorem geometry18_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.a := by decide +kernel
theorem weights36_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights37_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time18_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 10)=true := by decide +kernel
theorem r_reference18_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 0)=true := by decide +kernel
theorem a_reference18_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 1)=true := by decide +kernel
theorem rank_r_link18_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r18 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link18_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0002.a18.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a18 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints18 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell true ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r18 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile18_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link18_checked
    geometry18_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell false ReferenceProfileData.CoarseLowerShape.Batch0002.a18.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a18 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile18_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link18_checked
    geometry18_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks18_linked.1,←ranks18_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0002.r18.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a18.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0002.ordered18_checked hr ha ho
theorem frozen_frame18 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18 ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds ReferenceProfileData.CoarseLowerShape.Batch0002.a18.bounds
  · rw [←r_profile18_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile18_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry18_linked.2.2.2.2.1
  · exact geometry18_linked.2.2.2.2.2
  · exact r_reference18_checked
  · exact a_reference18_checked
  · exact r_fixed18_linked
  · exact a_fixed18_linked
  · exact time18_checked
  · exact ht
  · exact hw
theorem child_geometry18_checked : ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights18 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0004.cert36∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch4_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0004.cert37∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch4_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry18_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights36_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry18_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry18_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights37_linked j (List.mem_finRange j))
theorem actual_frozen_frame18 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame18 (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.flow.timeParameter_mem child_geometry18_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights18 hz)
theorem r_profile19_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r19=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds := by rfl
theorem a_profile19_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a19=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a19.bounds := by rfl
theorem r_fixed19_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 7 := by decide +kernel
theorem a_fixed19_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a19.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.a19.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 9 := by decide +kernel
theorem ranks19_linked : ReferenceRankData.CoarseLowerShape.Batch0002.targetR19=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0002.targetA19=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 1 := by decide +kernel
theorem r_input19_linked : ReferenceRankData.CoarseLowerShape.Batch0002.r19.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds.gauge] := by decide +kernel
theorem a_input19_linked : ReferenceRankData.CoarseLowerShape.Batch0002.a19.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.a19.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.a19.bounds.gauge] := by decide +kernel
theorem geometry19_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.a := by decide +kernel
theorem weights38_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights39_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time19_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 10)=true := by decide +kernel
theorem r_reference19_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 0)=true := by decide +kernel
theorem a_reference19_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 1)=true := by decide +kernel
theorem rank_r_link19_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r19 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link19_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0002.a19.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a19 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints19 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell true ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r19 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile19_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link19_checked
    geometry19_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell false ReferenceProfileData.CoarseLowerShape.Batch0002.a19.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a19 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile19_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link19_checked
    geometry19_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks19_linked.1,←ranks19_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0002.r19.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a19.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0002.ordered19_checked hr ha ho
theorem frozen_frame19 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19 ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds ReferenceProfileData.CoarseLowerShape.Batch0002.a19.bounds
  · rw [←r_profile19_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile19_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry19_linked.2.2.2.2.1
  · exact geometry19_linked.2.2.2.2.2
  · exact r_reference19_checked
  · exact a_reference19_checked
  · exact r_fixed19_linked
  · exact a_fixed19_linked
  · exact time19_checked
  · exact ht
  · exact hw
theorem child_geometry19_checked : ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights19 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0004.cert38∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch4_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0004.cert39∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch4_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0004.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry19_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights38_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry19_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry19_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights39_linked j (List.mem_finRange j))
theorem actual_frozen_frame19 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame19 (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.flow.timeParameter_mem child_geometry19_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights19 hz)
theorem r_profile20_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r20=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds := by rfl
theorem a_profile20_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a20=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a20.bounds := by rfl
theorem r_fixed20_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 7 := by decide +kernel
theorem a_fixed20_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a20.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.a20.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 9 := by decide +kernel
theorem ranks20_linked : ReferenceRankData.CoarseLowerShape.Batch0002.targetR20=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0002.targetA20=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 1 := by decide +kernel
theorem r_input20_linked : ReferenceRankData.CoarseLowerShape.Batch0002.r20.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds.gauge] := by decide +kernel
theorem a_input20_linked : ReferenceRankData.CoarseLowerShape.Batch0002.a20.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.a20.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.a20.bounds.gauge] := by decide +kernel
theorem geometry20_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.a := by decide +kernel
theorem weights40_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0005.cert40.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights41_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0005.cert41.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time20_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 10)=true := by decide +kernel
theorem r_reference20_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 0)=true := by decide +kernel
theorem a_reference20_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 1)=true := by decide +kernel
theorem rank_r_link20_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r20 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link20_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0002.a20.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a20 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints20 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell true ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r20 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile20_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link20_checked
    geometry20_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell false ReferenceProfileData.CoarseLowerShape.Batch0002.a20.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a20 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile20_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link20_checked
    geometry20_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks20_linked.1,←ranks20_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0002.r20.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a20.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0002.ordered20_checked hr ha ho
theorem frozen_frame20 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20 ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds ReferenceProfileData.CoarseLowerShape.Batch0002.a20.bounds
  · rw [←r_profile20_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile20_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry20_linked.2.2.2.2.1
  · exact geometry20_linked.2.2.2.2.2
  · exact r_reference20_checked
  · exact a_reference20_checked
  · exact r_fixed20_linked
  · exact a_fixed20_linked
  · exact time20_checked
  · exact ht
  · exact hw
theorem child_geometry20_checked : ReferenceWeightData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights20 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0005.cert40∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch5_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0005.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0005.cert41∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch5_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0005.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0005.cert40.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry20_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights40_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0005.cert41.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry20_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry20_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights41_linked j (List.mem_finRange j))
theorem actual_frozen_frame20 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame20 (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.flow.timeParameter_mem child_geometry20_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights20 hz)
theorem r_profile21_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r21=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds := by rfl
theorem a_profile21_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a21=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a21.bounds := by rfl
theorem r_fixed21_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 7 := by decide +kernel
theorem a_fixed21_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a21.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.a21.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 9 := by decide +kernel
theorem ranks21_linked : ReferenceRankData.CoarseLowerShape.Batch0002.targetR21=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0002.targetA21=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 1 := by decide +kernel
theorem r_input21_linked : ReferenceRankData.CoarseLowerShape.Batch0002.r21.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds.gauge] := by decide +kernel
theorem a_input21_linked : ReferenceRankData.CoarseLowerShape.Batch0002.a21.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.a21.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.a21.bounds.gauge] := by decide +kernel
theorem geometry21_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.a := by decide +kernel
theorem weights42_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0005.cert42.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights43_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0005.cert43.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time21_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 10)=true := by decide +kernel
theorem r_reference21_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 0)=true := by decide +kernel
theorem a_reference21_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 1)=true := by decide +kernel
theorem rank_r_link21_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r21 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link21_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0002.a21.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a21 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints21 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell true ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r21 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile21_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link21_checked
    geometry21_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell false ReferenceProfileData.CoarseLowerShape.Batch0002.a21.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a21 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile21_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link21_checked
    geometry21_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks21_linked.1,←ranks21_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0002.r21.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a21.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0002.ordered21_checked hr ha ho
theorem frozen_frame21 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21 ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds ReferenceProfileData.CoarseLowerShape.Batch0002.a21.bounds
  · rw [←r_profile21_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile21_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry21_linked.2.2.2.2.1
  · exact geometry21_linked.2.2.2.2.2
  · exact r_reference21_checked
  · exact a_reference21_checked
  · exact r_fixed21_linked
  · exact a_fixed21_linked
  · exact time21_checked
  · exact ht
  · exact hw
theorem child_geometry21_checked : ReferenceWeightData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights21 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0005.cert42∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch5_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0005.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0005.cert43∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch5_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0005.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0005.cert42.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry21_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights42_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0005.cert43.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry21_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry21_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights43_linked j (List.mem_finRange j))
theorem actual_frozen_frame21 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame21 (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.flow.timeParameter_mem child_geometry21_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights21 hz)
theorem r_profile22_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r22=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds := by rfl
theorem a_profile22_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a22=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a22.bounds := by rfl
theorem r_fixed22_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 7 := by decide +kernel
theorem a_fixed22_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a22.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.a22.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 9 := by decide +kernel
theorem ranks22_linked : ReferenceRankData.CoarseLowerShape.Batch0002.targetR22=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0002.targetA22=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 1 := by decide +kernel
theorem r_input22_linked : ReferenceRankData.CoarseLowerShape.Batch0002.r22.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds.gauge] := by decide +kernel
theorem a_input22_linked : ReferenceRankData.CoarseLowerShape.Batch0002.a22.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.a22.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.a22.bounds.gauge] := by decide +kernel
theorem geometry22_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.a := by decide +kernel
theorem weights44_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0005.cert44.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights45_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0005.cert45.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time22_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 10)=true := by decide +kernel
theorem r_reference22_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 0)=true := by decide +kernel
theorem a_reference22_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 1)=true := by decide +kernel
theorem rank_r_link22_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r22 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link22_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0002.a22.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a22 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints22 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell true ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r22 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile22_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link22_checked
    geometry22_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell false ReferenceProfileData.CoarseLowerShape.Batch0002.a22.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a22 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile22_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link22_checked
    geometry22_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks22_linked.1,←ranks22_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0002.r22.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a22.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0002.ordered22_checked hr ha ho
theorem frozen_frame22 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22 ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds ReferenceProfileData.CoarseLowerShape.Batch0002.a22.bounds
  · rw [←r_profile22_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile22_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry22_linked.2.2.2.2.1
  · exact geometry22_linked.2.2.2.2.2
  · exact r_reference22_checked
  · exact a_reference22_checked
  · exact r_fixed22_linked
  · exact a_fixed22_linked
  · exact time22_checked
  · exact ht
  · exact hw
theorem child_geometry22_checked : ReferenceWeightData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights22 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0005.cert44∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch5_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0005.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0005.cert45∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch5_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0005.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0005.cert44.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry22_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights44_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0005.cert45.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry22_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry22_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights45_linked j (List.mem_finRange j))
theorem actual_frozen_frame22 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame22 (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.flow.timeParameter_mem child_geometry22_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights22 hz)
theorem r_profile23_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r23=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds := by rfl
theorem a_profile23_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a23=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a23.bounds := by rfl
theorem r_fixed23_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 7 := by decide +kernel
theorem a_fixed23_linked : ReferenceProfileData.CoarseLowerShape.Batch0002.a23.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0002.a23.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 9 := by decide +kernel
theorem ranks23_linked : ReferenceRankData.CoarseLowerShape.Batch0002.targetR23=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0002.targetA23=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 1 := by decide +kernel
theorem r_input23_linked : ReferenceRankData.CoarseLowerShape.Batch0002.r23.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds.gauge] := by decide +kernel
theorem a_input23_linked : ReferenceRankData.CoarseLowerShape.Batch0002.a23.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0002.a23.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0002.a23.bounds.gauge] := by decide +kernel
theorem geometry23_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.a := by decide +kernel
theorem weights46_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0005.cert46.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights47_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0005.cert47.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time23_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 10)=true := by decide +kernel
theorem r_reference23_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 0)=true := by decide +kernel
theorem a_reference23_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 1)=true := by decide +kernel
theorem rank_r_link23_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r23 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link23_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0002.a23.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a23 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints23 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell true ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds ReferenceRankData.CoarseLowerShape.Batch0002.r23 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile23_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link23_checked
    geometry23_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell false ReferenceProfileData.CoarseLowerShape.Batch0002.a23.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a23 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile23_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0002.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0002.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link23_checked
    geometry23_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks23_linked.1,←ranks23_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0002.r23.bounds ReferenceRankData.CoarseLowerShape.Batch0002.a23.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0002.ordered23_checked hr ha ho
theorem frozen_frame23 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23 ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds ReferenceProfileData.CoarseLowerShape.Batch0002.a23.bounds
  · rw [←r_profile23_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile23_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry23_linked.2.2.2.2.1
  · exact geometry23_linked.2.2.2.2.2
  · exact r_reference23_checked
  · exact a_reference23_checked
  · exact r_fixed23_linked
  · exact a_fixed23_linked
  · exact time23_checked
  · exact ht
  · exact hw
theorem child_geometry23_checked : ReferenceWeightData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights23 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0005.cert46∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch5_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0005.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0005.cert47∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch5_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0005.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0005.cert46.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry23_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights46_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0005.cert47.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry23_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry23_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights47_linked j (List.mem_finRange j))
theorem actual_frozen_frame23 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame23 (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.flow.timeParameter_mem child_geometry23_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights23 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell16),(ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell17),(ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell18),(ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell19),(ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell20),(ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell21),(ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell22),(ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0002.cell23)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0002.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0002.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame16 hz
  · exact fun z hz=>actual_frozen_frame17 hz
  · exact fun z hz=>actual_frozen_frame18 hz
  · exact fun z hz=>actual_frozen_frame19 hz
  · exact fun z hz=>actual_frozen_frame20 hz
  · exact fun z hz=>actual_frozen_frame21 hz
  · exact fun z hz=>actual_frozen_frame22 hz
  · exact fun z hz=>actual_frozen_frame23 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints16 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints17 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints18 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints19 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints20 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints21 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints22 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints23 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry16_linked.1,geometry16_linked.2.1,geometry16_linked.2.2.1,geometry16_linked.2.2.2.1⟩
  · exact ⟨geometry17_linked.1,geometry17_linked.2.1,geometry17_linked.2.2.1,geometry17_linked.2.2.2.1⟩
  · exact ⟨geometry18_linked.1,geometry18_linked.2.1,geometry18_linked.2.2.1,geometry18_linked.2.2.2.1⟩
  · exact ⟨geometry19_linked.1,geometry19_linked.2.1,geometry19_linked.2.2.1,geometry19_linked.2.2.2.1⟩
  · exact ⟨geometry20_linked.1,geometry20_linked.2.1,geometry20_linked.2.2.1,geometry20_linked.2.2.2.1⟩
  · exact ⟨geometry21_linked.1,geometry21_linked.2.1,geometry21_linked.2.2.1,geometry21_linked.2.2.2.1⟩
  · exact ⟨geometry22_linked.1,geometry22_linked.2.1,geometry22_linked.2.2.1,geometry22_linked.2.2.2.1⟩
  · exact ⟨geometry23_linked.1,geometry23_linked.2.1,geometry23_linked.2.2.1,geometry23_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.a16.bounds,?_,geometry16_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a16.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile16_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds,?_,geometry16_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert16.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r16.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile16_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.a17.bounds,?_,geometry17_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a17.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile17_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds,?_,geometry17_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert17.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r17.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile17_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.a18.bounds,?_,geometry18_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a18.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile18_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds,?_,geometry18_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert18.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r18.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile18_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.a19.bounds,?_,geometry19_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a19.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile19_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds,?_,geometry19_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert19.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r19.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile19_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.a20.bounds,?_,geometry20_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a20.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile20_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds,?_,geometry20_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert20.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r20.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile20_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.a21.bounds,?_,geometry21_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a21.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile21_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds,?_,geometry21_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert21.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r21.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile21_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.a22.bounds,?_,geometry22_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a22.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile22_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds,?_,geometry22_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert22.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r22.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile22_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.a23.bounds,?_,geometry23_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0002.a23.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile23_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds,?_,geometry23_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0002.cert23.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0002.r23.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile23_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0002.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0002.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0002

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0003
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch6_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0006.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0006.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch7_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0007.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0007.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile24_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r24=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds := by rfl
theorem a_profile24_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a24=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a24.bounds := by rfl
theorem r_fixed24_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 7 := by decide +kernel
theorem a_fixed24_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a24.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.a24.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 9 := by decide +kernel
theorem ranks24_linked : ReferenceRankData.CoarseLowerShape.Batch0003.targetR24=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0003.targetA24=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 1 := by decide +kernel
theorem r_input24_linked : ReferenceRankData.CoarseLowerShape.Batch0003.r24.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds.gauge] := by decide +kernel
theorem a_input24_linked : ReferenceRankData.CoarseLowerShape.Batch0003.a24.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.a24.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.a24.bounds.gauge] := by decide +kernel
theorem geometry24_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.a := by decide +kernel
theorem weights48_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0006.cert48.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights49_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0006.cert49.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time24_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 10)=true := by decide +kernel
theorem r_reference24_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 0)=true := by decide +kernel
theorem a_reference24_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 1)=true := by decide +kernel
theorem rank_r_link24_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r24 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link24_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0003.a24.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a24 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints24 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell true ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r24 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile24_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link24_checked
    geometry24_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell false ReferenceProfileData.CoarseLowerShape.Batch0003.a24.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a24 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile24_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link24_checked
    geometry24_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks24_linked.1,←ranks24_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0003.r24.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a24.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0003.ordered24_checked hr ha ho
theorem frozen_frame24 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24 ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds ReferenceProfileData.CoarseLowerShape.Batch0003.a24.bounds
  · rw [←r_profile24_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile24_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry24_linked.2.2.2.2.1
  · exact geometry24_linked.2.2.2.2.2
  · exact r_reference24_checked
  · exact a_reference24_checked
  · exact r_fixed24_linked
  · exact a_fixed24_linked
  · exact time24_checked
  · exact ht
  · exact hw
theorem child_geometry24_checked : ReferenceWeightData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights24 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0006.cert48∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch6_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0006.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0006.cert49∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch6_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0006.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0006.cert48.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry24_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights48_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0006.cert49.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry24_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry24_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights49_linked j (List.mem_finRange j))
theorem actual_frozen_frame24 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame24 (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.flow.timeParameter_mem child_geometry24_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights24 hz)
theorem r_profile25_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r25=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds := by rfl
theorem a_profile25_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a25=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a25.bounds := by rfl
theorem r_fixed25_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 7 := by decide +kernel
theorem a_fixed25_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a25.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.a25.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 9 := by decide +kernel
theorem ranks25_linked : ReferenceRankData.CoarseLowerShape.Batch0003.targetR25=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0003.targetA25=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 1 := by decide +kernel
theorem r_input25_linked : ReferenceRankData.CoarseLowerShape.Batch0003.r25.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds.gauge] := by decide +kernel
theorem a_input25_linked : ReferenceRankData.CoarseLowerShape.Batch0003.a25.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.a25.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.a25.bounds.gauge] := by decide +kernel
theorem geometry25_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.a := by decide +kernel
theorem weights50_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0006.cert50.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights51_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0006.cert51.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time25_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 10)=true := by decide +kernel
theorem r_reference25_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 0)=true := by decide +kernel
theorem a_reference25_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 1)=true := by decide +kernel
theorem rank_r_link25_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r25 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link25_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0003.a25.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a25 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints25 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell true ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r25 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile25_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link25_checked
    geometry25_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell false ReferenceProfileData.CoarseLowerShape.Batch0003.a25.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a25 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile25_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link25_checked
    geometry25_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks25_linked.1,←ranks25_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0003.r25.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a25.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0003.ordered25_checked hr ha ho
theorem frozen_frame25 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25 ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds ReferenceProfileData.CoarseLowerShape.Batch0003.a25.bounds
  · rw [←r_profile25_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile25_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry25_linked.2.2.2.2.1
  · exact geometry25_linked.2.2.2.2.2
  · exact r_reference25_checked
  · exact a_reference25_checked
  · exact r_fixed25_linked
  · exact a_fixed25_linked
  · exact time25_checked
  · exact ht
  · exact hw
theorem child_geometry25_checked : ReferenceWeightData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights25 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0006.cert50∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch6_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0006.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0006.cert51∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch6_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0006.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0006.cert50.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry25_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights50_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0006.cert51.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry25_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry25_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights51_linked j (List.mem_finRange j))
theorem actual_frozen_frame25 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame25 (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.flow.timeParameter_mem child_geometry25_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights25 hz)
theorem r_profile26_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r26=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds := by rfl
theorem a_profile26_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a26=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a26.bounds := by rfl
theorem r_fixed26_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 7 := by decide +kernel
theorem a_fixed26_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a26.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.a26.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 9 := by decide +kernel
theorem ranks26_linked : ReferenceRankData.CoarseLowerShape.Batch0003.targetR26=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0003.targetA26=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 1 := by decide +kernel
theorem r_input26_linked : ReferenceRankData.CoarseLowerShape.Batch0003.r26.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds.gauge] := by decide +kernel
theorem a_input26_linked : ReferenceRankData.CoarseLowerShape.Batch0003.a26.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.a26.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.a26.bounds.gauge] := by decide +kernel
theorem geometry26_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.a := by decide +kernel
theorem weights52_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0006.cert52.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights53_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0006.cert53.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time26_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 10)=true := by decide +kernel
theorem r_reference26_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 0)=true := by decide +kernel
theorem a_reference26_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 1)=true := by decide +kernel
theorem rank_r_link26_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r26 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link26_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0003.a26.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a26 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints26 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell true ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r26 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile26_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link26_checked
    geometry26_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell false ReferenceProfileData.CoarseLowerShape.Batch0003.a26.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a26 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile26_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link26_checked
    geometry26_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks26_linked.1,←ranks26_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0003.r26.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a26.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0003.ordered26_checked hr ha ho
theorem frozen_frame26 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26 ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds ReferenceProfileData.CoarseLowerShape.Batch0003.a26.bounds
  · rw [←r_profile26_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile26_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry26_linked.2.2.2.2.1
  · exact geometry26_linked.2.2.2.2.2
  · exact r_reference26_checked
  · exact a_reference26_checked
  · exact r_fixed26_linked
  · exact a_fixed26_linked
  · exact time26_checked
  · exact ht
  · exact hw
theorem child_geometry26_checked : ReferenceWeightData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights26 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0006.cert52∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch6_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0006.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0006.cert53∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch6_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0006.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0006.cert52.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry26_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights52_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0006.cert53.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry26_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry26_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights53_linked j (List.mem_finRange j))
theorem actual_frozen_frame26 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame26 (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.flow.timeParameter_mem child_geometry26_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights26 hz)
theorem r_profile27_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r27=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds := by rfl
theorem a_profile27_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a27=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a27.bounds := by rfl
theorem r_fixed27_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 7 := by decide +kernel
theorem a_fixed27_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a27.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.a27.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 9 := by decide +kernel
theorem ranks27_linked : ReferenceRankData.CoarseLowerShape.Batch0003.targetR27=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0003.targetA27=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 1 := by decide +kernel
theorem r_input27_linked : ReferenceRankData.CoarseLowerShape.Batch0003.r27.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds.gauge] := by decide +kernel
theorem a_input27_linked : ReferenceRankData.CoarseLowerShape.Batch0003.a27.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.a27.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.a27.bounds.gauge] := by decide +kernel
theorem geometry27_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.a := by decide +kernel
theorem weights54_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0006.cert54.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights55_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0006.cert55.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time27_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 10)=true := by decide +kernel
theorem r_reference27_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 0)=true := by decide +kernel
theorem a_reference27_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 1)=true := by decide +kernel
theorem rank_r_link27_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r27 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link27_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0003.a27.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a27 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints27 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell true ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r27 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile27_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link27_checked
    geometry27_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell false ReferenceProfileData.CoarseLowerShape.Batch0003.a27.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a27 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile27_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link27_checked
    geometry27_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks27_linked.1,←ranks27_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0003.r27.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a27.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0003.ordered27_checked hr ha ho
theorem frozen_frame27 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27 ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds ReferenceProfileData.CoarseLowerShape.Batch0003.a27.bounds
  · rw [←r_profile27_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile27_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry27_linked.2.2.2.2.1
  · exact geometry27_linked.2.2.2.2.2
  · exact r_reference27_checked
  · exact a_reference27_checked
  · exact r_fixed27_linked
  · exact a_fixed27_linked
  · exact time27_checked
  · exact ht
  · exact hw
theorem child_geometry27_checked : ReferenceWeightData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights27 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0006.cert54∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch6_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0006.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0006.cert55∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch6_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0006.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0006.cert54.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry27_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights54_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0006.cert55.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry27_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry27_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights55_linked j (List.mem_finRange j))
theorem actual_frozen_frame27 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame27 (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.flow.timeParameter_mem child_geometry27_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights27 hz)
theorem r_profile28_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r28=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds := by rfl
theorem a_profile28_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a28=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a28.bounds := by rfl
theorem r_fixed28_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 7 := by decide +kernel
theorem a_fixed28_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a28.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.a28.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 9 := by decide +kernel
theorem ranks28_linked : ReferenceRankData.CoarseLowerShape.Batch0003.targetR28=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0003.targetA28=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 1 := by decide +kernel
theorem r_input28_linked : ReferenceRankData.CoarseLowerShape.Batch0003.r28.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds.gauge] := by decide +kernel
theorem a_input28_linked : ReferenceRankData.CoarseLowerShape.Batch0003.a28.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.a28.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.a28.bounds.gauge] := by decide +kernel
theorem geometry28_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.a := by decide +kernel
theorem weights56_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0007.cert56.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights57_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0007.cert57.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time28_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 10)=true := by decide +kernel
theorem r_reference28_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 0)=true := by decide +kernel
theorem a_reference28_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 1)=true := by decide +kernel
theorem rank_r_link28_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r28 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link28_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0003.a28.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a28 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints28 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell true ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r28 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile28_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link28_checked
    geometry28_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell false ReferenceProfileData.CoarseLowerShape.Batch0003.a28.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a28 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile28_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link28_checked
    geometry28_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks28_linked.1,←ranks28_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0003.r28.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a28.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0003.ordered28_checked hr ha ho
theorem frozen_frame28 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28 ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds ReferenceProfileData.CoarseLowerShape.Batch0003.a28.bounds
  · rw [←r_profile28_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile28_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry28_linked.2.2.2.2.1
  · exact geometry28_linked.2.2.2.2.2
  · exact r_reference28_checked
  · exact a_reference28_checked
  · exact r_fixed28_linked
  · exact a_fixed28_linked
  · exact time28_checked
  · exact ht
  · exact hw
theorem child_geometry28_checked : ReferenceWeightData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights28 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0007.cert56∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch7_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0007.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0007.cert57∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch7_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0007.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0007.cert56.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry28_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights56_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0007.cert57.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry28_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry28_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights57_linked j (List.mem_finRange j))
theorem actual_frozen_frame28 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame28 (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.flow.timeParameter_mem child_geometry28_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights28 hz)
theorem r_profile29_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r29=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds := by rfl
theorem a_profile29_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a29=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a29.bounds := by rfl
theorem r_fixed29_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 7 := by decide +kernel
theorem a_fixed29_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a29.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.a29.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 9 := by decide +kernel
theorem ranks29_linked : ReferenceRankData.CoarseLowerShape.Batch0003.targetR29=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0003.targetA29=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 1 := by decide +kernel
theorem r_input29_linked : ReferenceRankData.CoarseLowerShape.Batch0003.r29.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds.gauge] := by decide +kernel
theorem a_input29_linked : ReferenceRankData.CoarseLowerShape.Batch0003.a29.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.a29.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.a29.bounds.gauge] := by decide +kernel
theorem geometry29_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.a := by decide +kernel
theorem weights58_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0007.cert58.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights59_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0007.cert59.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time29_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 10)=true := by decide +kernel
theorem r_reference29_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 0)=true := by decide +kernel
theorem a_reference29_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 1)=true := by decide +kernel
theorem rank_r_link29_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r29 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link29_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0003.a29.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a29 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints29 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell true ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r29 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile29_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link29_checked
    geometry29_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell false ReferenceProfileData.CoarseLowerShape.Batch0003.a29.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a29 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile29_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link29_checked
    geometry29_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks29_linked.1,←ranks29_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0003.r29.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a29.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0003.ordered29_checked hr ha ho
theorem frozen_frame29 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29 ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds ReferenceProfileData.CoarseLowerShape.Batch0003.a29.bounds
  · rw [←r_profile29_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile29_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry29_linked.2.2.2.2.1
  · exact geometry29_linked.2.2.2.2.2
  · exact r_reference29_checked
  · exact a_reference29_checked
  · exact r_fixed29_linked
  · exact a_fixed29_linked
  · exact time29_checked
  · exact ht
  · exact hw
theorem child_geometry29_checked : ReferenceWeightData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights29 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0007.cert58∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch7_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0007.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0007.cert59∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch7_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0007.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0007.cert58.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry29_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights58_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0007.cert59.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry29_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry29_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights59_linked j (List.mem_finRange j))
theorem actual_frozen_frame29 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame29 (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.flow.timeParameter_mem child_geometry29_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights29 hz)
theorem r_profile30_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r30=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds := by rfl
theorem a_profile30_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a30=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a30.bounds := by rfl
theorem r_fixed30_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 7 := by decide +kernel
theorem a_fixed30_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a30.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.a30.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 9 := by decide +kernel
theorem ranks30_linked : ReferenceRankData.CoarseLowerShape.Batch0003.targetR30=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0003.targetA30=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 1 := by decide +kernel
theorem r_input30_linked : ReferenceRankData.CoarseLowerShape.Batch0003.r30.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds.gauge] := by decide +kernel
theorem a_input30_linked : ReferenceRankData.CoarseLowerShape.Batch0003.a30.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.a30.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.a30.bounds.gauge] := by decide +kernel
theorem geometry30_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.a := by decide +kernel
theorem weights60_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0007.cert60.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights61_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0007.cert61.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time30_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 10)=true := by decide +kernel
theorem r_reference30_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 0)=true := by decide +kernel
theorem a_reference30_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 1)=true := by decide +kernel
theorem rank_r_link30_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r30 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link30_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0003.a30.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a30 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints30 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell true ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r30 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile30_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link30_checked
    geometry30_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell false ReferenceProfileData.CoarseLowerShape.Batch0003.a30.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a30 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile30_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link30_checked
    geometry30_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks30_linked.1,←ranks30_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0003.r30.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a30.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0003.ordered30_checked hr ha ho
theorem frozen_frame30 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30 ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds ReferenceProfileData.CoarseLowerShape.Batch0003.a30.bounds
  · rw [←r_profile30_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile30_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry30_linked.2.2.2.2.1
  · exact geometry30_linked.2.2.2.2.2
  · exact r_reference30_checked
  · exact a_reference30_checked
  · exact r_fixed30_linked
  · exact a_fixed30_linked
  · exact time30_checked
  · exact ht
  · exact hw
theorem child_geometry30_checked : ReferenceWeightData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights30 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0007.cert60∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch7_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0007.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0007.cert61∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch7_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0007.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0007.cert60.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry30_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights60_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0007.cert61.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry30_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry30_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights61_linked j (List.mem_finRange j))
theorem actual_frozen_frame30 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame30 (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.flow.timeParameter_mem child_geometry30_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights30 hz)
theorem r_profile31_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r31=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds := by rfl
theorem a_profile31_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a31=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a31.bounds := by rfl
theorem r_fixed31_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 7 := by decide +kernel
theorem a_fixed31_linked : ReferenceProfileData.CoarseLowerShape.Batch0003.a31.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0003.a31.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 9 := by decide +kernel
theorem ranks31_linked : ReferenceRankData.CoarseLowerShape.Batch0003.targetR31=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0003.targetA31=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 1 := by decide +kernel
theorem r_input31_linked : ReferenceRankData.CoarseLowerShape.Batch0003.r31.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds.gauge] := by decide +kernel
theorem a_input31_linked : ReferenceRankData.CoarseLowerShape.Batch0003.a31.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0003.a31.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0003.a31.bounds.gauge] := by decide +kernel
theorem geometry31_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.a := by decide +kernel
theorem weights62_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0007.cert62.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights63_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0007.cert63.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time31_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 10)=true := by decide +kernel
theorem r_reference31_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 0)=true := by decide +kernel
theorem a_reference31_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 1)=true := by decide +kernel
theorem rank_r_link31_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r31 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link31_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0003.a31.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a31 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints31 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell true ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds ReferenceRankData.CoarseLowerShape.Batch0003.r31 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile31_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link31_checked
    geometry31_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell false ReferenceProfileData.CoarseLowerShape.Batch0003.a31.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a31 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile31_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0003.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0003.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link31_checked
    geometry31_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks31_linked.1,←ranks31_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0003.r31.bounds ReferenceRankData.CoarseLowerShape.Batch0003.a31.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0003.ordered31_checked hr ha ho
theorem frozen_frame31 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31 ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds ReferenceProfileData.CoarseLowerShape.Batch0003.a31.bounds
  · rw [←r_profile31_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile31_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry31_linked.2.2.2.2.1
  · exact geometry31_linked.2.2.2.2.2
  · exact r_reference31_checked
  · exact a_reference31_checked
  · exact r_fixed31_linked
  · exact a_fixed31_linked
  · exact time31_checked
  · exact ht
  · exact hw
theorem child_geometry31_checked : ReferenceWeightData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights31 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0007.cert62∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch7_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0007.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0007.cert63∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch7_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0007.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0007.cert62.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry31_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights62_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0007.cert63.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry31_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry31_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights63_linked j (List.mem_finRange j))
theorem actual_frozen_frame31 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame31 (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.flow.timeParameter_mem child_geometry31_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights31 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell24),(ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell25),(ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell26),(ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell27),(ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell28),(ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell29),(ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell30),(ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0003.cell31)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0003.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0003.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame24 hz
  · exact fun z hz=>actual_frozen_frame25 hz
  · exact fun z hz=>actual_frozen_frame26 hz
  · exact fun z hz=>actual_frozen_frame27 hz
  · exact fun z hz=>actual_frozen_frame28 hz
  · exact fun z hz=>actual_frozen_frame29 hz
  · exact fun z hz=>actual_frozen_frame30 hz
  · exact fun z hz=>actual_frozen_frame31 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints24 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints25 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints26 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints27 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints28 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints29 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints30 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints31 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry24_linked.1,geometry24_linked.2.1,geometry24_linked.2.2.1,geometry24_linked.2.2.2.1⟩
  · exact ⟨geometry25_linked.1,geometry25_linked.2.1,geometry25_linked.2.2.1,geometry25_linked.2.2.2.1⟩
  · exact ⟨geometry26_linked.1,geometry26_linked.2.1,geometry26_linked.2.2.1,geometry26_linked.2.2.2.1⟩
  · exact ⟨geometry27_linked.1,geometry27_linked.2.1,geometry27_linked.2.2.1,geometry27_linked.2.2.2.1⟩
  · exact ⟨geometry28_linked.1,geometry28_linked.2.1,geometry28_linked.2.2.1,geometry28_linked.2.2.2.1⟩
  · exact ⟨geometry29_linked.1,geometry29_linked.2.1,geometry29_linked.2.2.1,geometry29_linked.2.2.2.1⟩
  · exact ⟨geometry30_linked.1,geometry30_linked.2.1,geometry30_linked.2.2.1,geometry30_linked.2.2.2.1⟩
  · exact ⟨geometry31_linked.1,geometry31_linked.2.1,geometry31_linked.2.2.1,geometry31_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.a24.bounds,?_,geometry24_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a24.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile24_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds,?_,geometry24_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert24.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r24.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile24_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.a25.bounds,?_,geometry25_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a25.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile25_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds,?_,geometry25_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert25.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r25.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile25_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.a26.bounds,?_,geometry26_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a26.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile26_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds,?_,geometry26_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert26.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r26.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile26_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.a27.bounds,?_,geometry27_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a27.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile27_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds,?_,geometry27_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert27.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r27.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile27_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.a28.bounds,?_,geometry28_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a28.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile28_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds,?_,geometry28_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert28.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r28.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile28_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.a29.bounds,?_,geometry29_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a29.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile29_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds,?_,geometry29_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert29.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r29.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile29_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.a30.bounds,?_,geometry30_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a30.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile30_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds,?_,geometry30_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert30.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r30.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile30_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.a31.bounds,?_,geometry31_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0003.a31.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile31_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds,?_,geometry31_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0003.cert31.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0003.r31.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile31_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0003.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0003.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0003

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0004
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch8_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0008.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0008.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch9_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0009.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0009.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile32_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r32=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds := by rfl
theorem a_profile32_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a32=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a32.bounds := by rfl
theorem r_fixed32_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 7 := by decide +kernel
theorem a_fixed32_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a32.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.a32.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 9 := by decide +kernel
theorem ranks32_linked : ReferenceRankData.CoarseLowerShape.Batch0004.targetR32=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0004.targetA32=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 1 := by decide +kernel
theorem r_input32_linked : ReferenceRankData.CoarseLowerShape.Batch0004.r32.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds.gauge] := by decide +kernel
theorem a_input32_linked : ReferenceRankData.CoarseLowerShape.Batch0004.a32.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.a32.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.a32.bounds.gauge] := by decide +kernel
theorem geometry32_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.a := by decide +kernel
theorem weights64_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0008.cert64.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights65_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0008.cert65.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time32_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 10)=true := by decide +kernel
theorem r_reference32_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 0)=true := by decide +kernel
theorem a_reference32_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 1)=true := by decide +kernel
theorem rank_r_link32_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r32 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link32_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0004.a32.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a32 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints32 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell true ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r32 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile32_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link32_checked
    geometry32_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell false ReferenceProfileData.CoarseLowerShape.Batch0004.a32.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a32 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile32_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link32_checked
    geometry32_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks32_linked.1,←ranks32_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0004.r32.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a32.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0004.ordered32_checked hr ha ho
theorem frozen_frame32 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32 ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds ReferenceProfileData.CoarseLowerShape.Batch0004.a32.bounds
  · rw [←r_profile32_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile32_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry32_linked.2.2.2.2.1
  · exact geometry32_linked.2.2.2.2.2
  · exact r_reference32_checked
  · exact a_reference32_checked
  · exact r_fixed32_linked
  · exact a_fixed32_linked
  · exact time32_checked
  · exact ht
  · exact hw
theorem child_geometry32_checked : ReferenceWeightData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights32 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0008.cert64∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch8_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0008.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0008.cert65∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch8_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0008.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry32_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights64_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry32_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry32_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights65_linked j (List.mem_finRange j))
theorem actual_frozen_frame32 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame32 (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.flow.timeParameter_mem child_geometry32_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights32 hz)
theorem r_profile33_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r33=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds := by rfl
theorem a_profile33_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a33=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a33.bounds := by rfl
theorem r_fixed33_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 7 := by decide +kernel
theorem a_fixed33_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a33.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.a33.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 9 := by decide +kernel
theorem ranks33_linked : ReferenceRankData.CoarseLowerShape.Batch0004.targetR33=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0004.targetA33=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 1 := by decide +kernel
theorem r_input33_linked : ReferenceRankData.CoarseLowerShape.Batch0004.r33.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds.gauge] := by decide +kernel
theorem a_input33_linked : ReferenceRankData.CoarseLowerShape.Batch0004.a33.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.a33.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.a33.bounds.gauge] := by decide +kernel
theorem geometry33_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.a := by decide +kernel
theorem weights66_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0008.cert66.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights67_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0008.cert67.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time33_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 10)=true := by decide +kernel
theorem r_reference33_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 0)=true := by decide +kernel
theorem a_reference33_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 1)=true := by decide +kernel
theorem rank_r_link33_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r33 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link33_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0004.a33.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a33 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints33 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell true ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r33 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile33_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link33_checked
    geometry33_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell false ReferenceProfileData.CoarseLowerShape.Batch0004.a33.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a33 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile33_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link33_checked
    geometry33_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks33_linked.1,←ranks33_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0004.r33.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a33.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0004.ordered33_checked hr ha ho
theorem frozen_frame33 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33 ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds ReferenceProfileData.CoarseLowerShape.Batch0004.a33.bounds
  · rw [←r_profile33_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile33_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry33_linked.2.2.2.2.1
  · exact geometry33_linked.2.2.2.2.2
  · exact r_reference33_checked
  · exact a_reference33_checked
  · exact r_fixed33_linked
  · exact a_fixed33_linked
  · exact time33_checked
  · exact ht
  · exact hw
theorem child_geometry33_checked : ReferenceWeightData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights33 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0008.cert66∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch8_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0008.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0008.cert67∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch8_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0008.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry33_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights66_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry33_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry33_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights67_linked j (List.mem_finRange j))
theorem actual_frozen_frame33 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame33 (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.flow.timeParameter_mem child_geometry33_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights33 hz)
theorem r_profile34_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r34=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds := by rfl
theorem a_profile34_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a34=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a34.bounds := by rfl
theorem r_fixed34_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 7 := by decide +kernel
theorem a_fixed34_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a34.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.a34.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 9 := by decide +kernel
theorem ranks34_linked : ReferenceRankData.CoarseLowerShape.Batch0004.targetR34=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0004.targetA34=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 1 := by decide +kernel
theorem r_input34_linked : ReferenceRankData.CoarseLowerShape.Batch0004.r34.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds.gauge] := by decide +kernel
theorem a_input34_linked : ReferenceRankData.CoarseLowerShape.Batch0004.a34.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.a34.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.a34.bounds.gauge] := by decide +kernel
theorem geometry34_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.a := by decide +kernel
theorem weights68_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0008.cert68.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights69_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0008.cert69.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time34_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 10)=true := by decide +kernel
theorem r_reference34_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 0)=true := by decide +kernel
theorem a_reference34_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 1)=true := by decide +kernel
theorem rank_r_link34_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r34 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link34_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0004.a34.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a34 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints34 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell true ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r34 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile34_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link34_checked
    geometry34_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell false ReferenceProfileData.CoarseLowerShape.Batch0004.a34.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a34 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile34_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link34_checked
    geometry34_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks34_linked.1,←ranks34_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0004.r34.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a34.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0004.ordered34_checked hr ha ho
theorem frozen_frame34 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34 ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds ReferenceProfileData.CoarseLowerShape.Batch0004.a34.bounds
  · rw [←r_profile34_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile34_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry34_linked.2.2.2.2.1
  · exact geometry34_linked.2.2.2.2.2
  · exact r_reference34_checked
  · exact a_reference34_checked
  · exact r_fixed34_linked
  · exact a_fixed34_linked
  · exact time34_checked
  · exact ht
  · exact hw
theorem child_geometry34_checked : ReferenceWeightData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights34 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0008.cert68∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch8_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0008.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0008.cert69∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch8_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0008.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry34_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights68_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry34_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry34_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights69_linked j (List.mem_finRange j))
theorem actual_frozen_frame34 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame34 (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.flow.timeParameter_mem child_geometry34_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights34 hz)
theorem r_profile35_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r35=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds := by rfl
theorem a_profile35_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a35=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a35.bounds := by rfl
theorem r_fixed35_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 7 := by decide +kernel
theorem a_fixed35_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a35.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.a35.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 9 := by decide +kernel
theorem ranks35_linked : ReferenceRankData.CoarseLowerShape.Batch0004.targetR35=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0004.targetA35=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 1 := by decide +kernel
theorem r_input35_linked : ReferenceRankData.CoarseLowerShape.Batch0004.r35.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds.gauge] := by decide +kernel
theorem a_input35_linked : ReferenceRankData.CoarseLowerShape.Batch0004.a35.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.a35.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.a35.bounds.gauge] := by decide +kernel
theorem geometry35_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.a := by decide +kernel
theorem weights70_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0008.cert70.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights71_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0008.cert71.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time35_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 10)=true := by decide +kernel
theorem r_reference35_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 0)=true := by decide +kernel
theorem a_reference35_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 1)=true := by decide +kernel
theorem rank_r_link35_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r35 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link35_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0004.a35.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a35 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints35 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell true ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r35 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile35_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link35_checked
    geometry35_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell false ReferenceProfileData.CoarseLowerShape.Batch0004.a35.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a35 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile35_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link35_checked
    geometry35_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks35_linked.1,←ranks35_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0004.r35.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a35.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0004.ordered35_checked hr ha ho
theorem frozen_frame35 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35 ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds ReferenceProfileData.CoarseLowerShape.Batch0004.a35.bounds
  · rw [←r_profile35_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile35_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry35_linked.2.2.2.2.1
  · exact geometry35_linked.2.2.2.2.2
  · exact r_reference35_checked
  · exact a_reference35_checked
  · exact r_fixed35_linked
  · exact a_fixed35_linked
  · exact time35_checked
  · exact ht
  · exact hw
theorem child_geometry35_checked : ReferenceWeightData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights35 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0008.cert70∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch8_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0008.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0008.cert71∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch8_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0008.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry35_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights70_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry35_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry35_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights71_linked j (List.mem_finRange j))
theorem actual_frozen_frame35 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame35 (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.flow.timeParameter_mem child_geometry35_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights35 hz)
theorem r_profile36_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r36=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds := by rfl
theorem a_profile36_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a36=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a36.bounds := by rfl
theorem r_fixed36_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 7 := by decide +kernel
theorem a_fixed36_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a36.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.a36.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 9 := by decide +kernel
theorem ranks36_linked : ReferenceRankData.CoarseLowerShape.Batch0004.targetR36=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0004.targetA36=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 1 := by decide +kernel
theorem r_input36_linked : ReferenceRankData.CoarseLowerShape.Batch0004.r36.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds.gauge] := by decide +kernel
theorem a_input36_linked : ReferenceRankData.CoarseLowerShape.Batch0004.a36.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.a36.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.a36.bounds.gauge] := by decide +kernel
theorem geometry36_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.a := by decide +kernel
theorem weights72_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0009.cert72.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights73_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0009.cert73.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time36_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 10)=true := by decide +kernel
theorem r_reference36_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 0)=true := by decide +kernel
theorem a_reference36_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 1)=true := by decide +kernel
theorem rank_r_link36_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r36 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link36_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0004.a36.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a36 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints36 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell true ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r36 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile36_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link36_checked
    geometry36_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell false ReferenceProfileData.CoarseLowerShape.Batch0004.a36.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a36 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile36_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link36_checked
    geometry36_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks36_linked.1,←ranks36_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0004.r36.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a36.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0004.ordered36_checked hr ha ho
theorem frozen_frame36 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36 ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds ReferenceProfileData.CoarseLowerShape.Batch0004.a36.bounds
  · rw [←r_profile36_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile36_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry36_linked.2.2.2.2.1
  · exact geometry36_linked.2.2.2.2.2
  · exact r_reference36_checked
  · exact a_reference36_checked
  · exact r_fixed36_linked
  · exact a_fixed36_linked
  · exact time36_checked
  · exact ht
  · exact hw
theorem child_geometry36_checked : ReferenceWeightData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights36 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0009.cert72∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch9_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0009.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0009.cert73∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch9_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0009.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry36_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights72_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry36_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry36_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights73_linked j (List.mem_finRange j))
theorem actual_frozen_frame36 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame36 (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.flow.timeParameter_mem child_geometry36_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights36 hz)
theorem r_profile37_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r37=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds := by rfl
theorem a_profile37_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a37=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a37.bounds := by rfl
theorem r_fixed37_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 7 := by decide +kernel
theorem a_fixed37_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a37.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.a37.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 9 := by decide +kernel
theorem ranks37_linked : ReferenceRankData.CoarseLowerShape.Batch0004.targetR37=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0004.targetA37=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 1 := by decide +kernel
theorem r_input37_linked : ReferenceRankData.CoarseLowerShape.Batch0004.r37.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds.gauge] := by decide +kernel
theorem a_input37_linked : ReferenceRankData.CoarseLowerShape.Batch0004.a37.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.a37.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.a37.bounds.gauge] := by decide +kernel
theorem geometry37_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.a := by decide +kernel
theorem weights74_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0009.cert74.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights75_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0009.cert75.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time37_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 10)=true := by decide +kernel
theorem r_reference37_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 0)=true := by decide +kernel
theorem a_reference37_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 1)=true := by decide +kernel
theorem rank_r_link37_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r37 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link37_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0004.a37.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a37 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints37 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell true ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r37 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile37_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link37_checked
    geometry37_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell false ReferenceProfileData.CoarseLowerShape.Batch0004.a37.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a37 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile37_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link37_checked
    geometry37_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks37_linked.1,←ranks37_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0004.r37.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a37.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0004.ordered37_checked hr ha ho
theorem frozen_frame37 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37 ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds ReferenceProfileData.CoarseLowerShape.Batch0004.a37.bounds
  · rw [←r_profile37_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile37_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry37_linked.2.2.2.2.1
  · exact geometry37_linked.2.2.2.2.2
  · exact r_reference37_checked
  · exact a_reference37_checked
  · exact r_fixed37_linked
  · exact a_fixed37_linked
  · exact time37_checked
  · exact ht
  · exact hw
theorem child_geometry37_checked : ReferenceWeightData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights37 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0009.cert74∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch9_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0009.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0009.cert75∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch9_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0009.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry37_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights74_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry37_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry37_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights75_linked j (List.mem_finRange j))
theorem actual_frozen_frame37 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame37 (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.flow.timeParameter_mem child_geometry37_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights37 hz)
theorem r_profile38_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r38=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds := by rfl
theorem a_profile38_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a38=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a38.bounds := by rfl
theorem r_fixed38_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 7 := by decide +kernel
theorem a_fixed38_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a38.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.a38.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 9 := by decide +kernel
theorem ranks38_linked : ReferenceRankData.CoarseLowerShape.Batch0004.targetR38=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0004.targetA38=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 1 := by decide +kernel
theorem r_input38_linked : ReferenceRankData.CoarseLowerShape.Batch0004.r38.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds.gauge] := by decide +kernel
theorem a_input38_linked : ReferenceRankData.CoarseLowerShape.Batch0004.a38.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.a38.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.a38.bounds.gauge] := by decide +kernel
theorem geometry38_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.a := by decide +kernel
theorem weights76_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0009.cert76.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights77_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0009.cert77.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time38_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 10)=true := by decide +kernel
theorem r_reference38_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 0)=true := by decide +kernel
theorem a_reference38_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 1)=true := by decide +kernel
theorem rank_r_link38_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r38 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link38_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0004.a38.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a38 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints38 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell true ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r38 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile38_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link38_checked
    geometry38_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell false ReferenceProfileData.CoarseLowerShape.Batch0004.a38.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a38 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile38_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link38_checked
    geometry38_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks38_linked.1,←ranks38_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0004.r38.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a38.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0004.ordered38_checked hr ha ho
theorem frozen_frame38 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38 ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds ReferenceProfileData.CoarseLowerShape.Batch0004.a38.bounds
  · rw [←r_profile38_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile38_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry38_linked.2.2.2.2.1
  · exact geometry38_linked.2.2.2.2.2
  · exact r_reference38_checked
  · exact a_reference38_checked
  · exact r_fixed38_linked
  · exact a_fixed38_linked
  · exact time38_checked
  · exact ht
  · exact hw
theorem child_geometry38_checked : ReferenceWeightData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights38 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0009.cert76∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch9_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0009.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0009.cert77∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch9_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0009.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry38_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights76_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry38_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry38_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights77_linked j (List.mem_finRange j))
theorem actual_frozen_frame38 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame38 (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.flow.timeParameter_mem child_geometry38_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights38 hz)
theorem r_profile39_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r39=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds := by rfl
theorem a_profile39_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a39=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a39.bounds := by rfl
theorem r_fixed39_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 7 := by decide +kernel
theorem a_fixed39_linked : ReferenceProfileData.CoarseLowerShape.Batch0004.a39.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0004.a39.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 9 := by decide +kernel
theorem ranks39_linked : ReferenceRankData.CoarseLowerShape.Batch0004.targetR39=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0004.targetA39=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 1 := by decide +kernel
theorem r_input39_linked : ReferenceRankData.CoarseLowerShape.Batch0004.r39.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds.gauge] := by decide +kernel
theorem a_input39_linked : ReferenceRankData.CoarseLowerShape.Batch0004.a39.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0004.a39.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0004.a39.bounds.gauge] := by decide +kernel
theorem geometry39_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.a := by decide +kernel
theorem weights78_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0009.cert78.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights79_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0009.cert79.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time39_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 10)=true := by decide +kernel
theorem r_reference39_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 0)=true := by decide +kernel
theorem a_reference39_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 1)=true := by decide +kernel
theorem rank_r_link39_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r39 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link39_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0004.a39.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a39 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints39 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell true ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds ReferenceRankData.CoarseLowerShape.Batch0004.r39 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile39_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link39_checked
    geometry39_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell false ReferenceProfileData.CoarseLowerShape.Batch0004.a39.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a39 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile39_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0004.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0004.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link39_checked
    geometry39_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks39_linked.1,←ranks39_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0004.r39.bounds ReferenceRankData.CoarseLowerShape.Batch0004.a39.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0004.ordered39_checked hr ha ho
theorem frozen_frame39 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39 ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds ReferenceProfileData.CoarseLowerShape.Batch0004.a39.bounds
  · rw [←r_profile39_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile39_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry39_linked.2.2.2.2.1
  · exact geometry39_linked.2.2.2.2.2
  · exact r_reference39_checked
  · exact a_reference39_checked
  · exact r_fixed39_linked
  · exact a_fixed39_linked
  · exact time39_checked
  · exact ht
  · exact hw
theorem child_geometry39_checked : ReferenceWeightData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights39 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0009.cert78∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch9_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0009.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0009.cert79∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch9_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0009.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry39_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights78_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry39_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry39_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights79_linked j (List.mem_finRange j))
theorem actual_frozen_frame39 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame39 (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.flow.timeParameter_mem child_geometry39_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights39 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell32),(ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell33),(ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell34),(ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell35),(ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell36),(ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell37),(ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell38),(ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0004.cell39)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0004.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0004.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame32 hz
  · exact fun z hz=>actual_frozen_frame33 hz
  · exact fun z hz=>actual_frozen_frame34 hz
  · exact fun z hz=>actual_frozen_frame35 hz
  · exact fun z hz=>actual_frozen_frame36 hz
  · exact fun z hz=>actual_frozen_frame37 hz
  · exact fun z hz=>actual_frozen_frame38 hz
  · exact fun z hz=>actual_frozen_frame39 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints32 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints33 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints34 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints35 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints36 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints37 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints38 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints39 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry32_linked.1,geometry32_linked.2.1,geometry32_linked.2.2.1,geometry32_linked.2.2.2.1⟩
  · exact ⟨geometry33_linked.1,geometry33_linked.2.1,geometry33_linked.2.2.1,geometry33_linked.2.2.2.1⟩
  · exact ⟨geometry34_linked.1,geometry34_linked.2.1,geometry34_linked.2.2.1,geometry34_linked.2.2.2.1⟩
  · exact ⟨geometry35_linked.1,geometry35_linked.2.1,geometry35_linked.2.2.1,geometry35_linked.2.2.2.1⟩
  · exact ⟨geometry36_linked.1,geometry36_linked.2.1,geometry36_linked.2.2.1,geometry36_linked.2.2.2.1⟩
  · exact ⟨geometry37_linked.1,geometry37_linked.2.1,geometry37_linked.2.2.1,geometry37_linked.2.2.2.1⟩
  · exact ⟨geometry38_linked.1,geometry38_linked.2.1,geometry38_linked.2.2.1,geometry38_linked.2.2.2.1⟩
  · exact ⟨geometry39_linked.1,geometry39_linked.2.1,geometry39_linked.2.2.1,geometry39_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.a32.bounds,?_,geometry32_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a32.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile32_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds,?_,geometry32_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert32.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r32.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile32_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.a33.bounds,?_,geometry33_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a33.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile33_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds,?_,geometry33_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert33.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r33.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile33_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.a34.bounds,?_,geometry34_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a34.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile34_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds,?_,geometry34_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert34.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r34.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile34_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.a35.bounds,?_,geometry35_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a35.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile35_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds,?_,geometry35_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert35.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r35.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile35_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.a36.bounds,?_,geometry36_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a36.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile36_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds,?_,geometry36_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert36.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r36.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile36_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.a37.bounds,?_,geometry37_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a37.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile37_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds,?_,geometry37_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert37.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r37.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile37_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.a38.bounds,?_,geometry38_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a38.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile38_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds,?_,geometry38_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert38.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r38.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile38_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.a39.bounds,?_,geometry39_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0004.a39.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile39_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds,?_,geometry39_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0004.cert39.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0004.r39.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile39_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0004.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0004.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0004
