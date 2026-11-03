import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0025_0028
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0025_0028
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0057_0060
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0026_0029
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0027_0030
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Bundle0024_0027
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0029_0032
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0029_0032
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0061_0064
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0030_0033
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0031_0034

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0028
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch56_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0056.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0056.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch57_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0057.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0057.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile224_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r224=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds := by rfl
theorem a_profile224_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a224=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a224.bounds := by rfl
theorem r_fixed224_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 7 := by decide +kernel
theorem a_fixed224_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a224.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.a224.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 9 := by decide +kernel
theorem ranks224_linked : ReferenceRankData.CoarseLowerShape.Batch0028.targetR224=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0028.targetA224=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 1 := by decide +kernel
theorem r_input224_linked : ReferenceRankData.CoarseLowerShape.Batch0028.r224.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds.gauge] := by decide +kernel
theorem a_input224_linked : ReferenceRankData.CoarseLowerShape.Batch0028.a224.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.a224.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.a224.bounds.gauge] := by decide +kernel
theorem geometry224_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.a := by decide +kernel
theorem weights448_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0056.cert448.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights449_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0056.cert449.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time224_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 10)=true := by decide +kernel
theorem r_reference224_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 0)=true := by decide +kernel
theorem a_reference224_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 1)=true := by decide +kernel
theorem rank_r_link224_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r224 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link224_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0028.a224.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a224 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints224 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell true ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r224 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile224_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link224_checked
    geometry224_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell false ReferenceProfileData.CoarseLowerShape.Batch0028.a224.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a224 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile224_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link224_checked
    geometry224_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks224_linked.1,←ranks224_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0028.r224.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a224.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0028.ordered224_checked hr ha ho
theorem frozen_frame224 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224 ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds ReferenceProfileData.CoarseLowerShape.Batch0028.a224.bounds
  · rw [←r_profile224_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile224_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry224_linked.2.2.2.2.1
  · exact geometry224_linked.2.2.2.2.2
  · exact r_reference224_checked
  · exact a_reference224_checked
  · exact r_fixed224_linked
  · exact a_fixed224_linked
  · exact time224_checked
  · exact ht
  · exact hw
theorem child_geometry224_checked : ReferenceWeightData.CoarseLowerShape.Batch0056.cert448.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0056.cert448.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0056.cert449.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0056.cert449.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights224 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0056.cert448∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch56_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0056.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0056.cert449∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch56_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0056.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0056.cert448.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0056.cert448.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0056.cert448.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry224_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights448_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0056.cert449.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0056.cert449.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry224_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry224_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights449_linked j (List.mem_finRange j))
theorem actual_frozen_frame224 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame224 (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.flow.timeParameter_mem child_geometry224_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights224 hz)
theorem r_profile225_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r225=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds := by rfl
theorem a_profile225_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a225=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a225.bounds := by rfl
theorem r_fixed225_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 7 := by decide +kernel
theorem a_fixed225_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a225.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.a225.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 9 := by decide +kernel
theorem ranks225_linked : ReferenceRankData.CoarseLowerShape.Batch0028.targetR225=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0028.targetA225=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 1 := by decide +kernel
theorem r_input225_linked : ReferenceRankData.CoarseLowerShape.Batch0028.r225.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds.gauge] := by decide +kernel
theorem a_input225_linked : ReferenceRankData.CoarseLowerShape.Batch0028.a225.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.a225.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.a225.bounds.gauge] := by decide +kernel
theorem geometry225_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.a := by decide +kernel
theorem weights450_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0056.cert450.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights451_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0056.cert451.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time225_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 10)=true := by decide +kernel
theorem r_reference225_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 0)=true := by decide +kernel
theorem a_reference225_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 1)=true := by decide +kernel
theorem rank_r_link225_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r225 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link225_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0028.a225.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a225 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints225 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell true ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r225 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile225_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link225_checked
    geometry225_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell false ReferenceProfileData.CoarseLowerShape.Batch0028.a225.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a225 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile225_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link225_checked
    geometry225_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks225_linked.1,←ranks225_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0028.r225.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a225.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0028.ordered225_checked hr ha ho
theorem frozen_frame225 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225 ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds ReferenceProfileData.CoarseLowerShape.Batch0028.a225.bounds
  · rw [←r_profile225_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile225_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry225_linked.2.2.2.2.1
  · exact geometry225_linked.2.2.2.2.2
  · exact r_reference225_checked
  · exact a_reference225_checked
  · exact r_fixed225_linked
  · exact a_fixed225_linked
  · exact time225_checked
  · exact ht
  · exact hw
theorem child_geometry225_checked : ReferenceWeightData.CoarseLowerShape.Batch0056.cert450.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0056.cert450.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0056.cert451.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0056.cert451.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights225 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0056.cert450∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch56_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0056.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0056.cert451∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch56_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0056.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0056.cert450.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0056.cert450.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0056.cert450.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry225_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights450_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0056.cert451.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0056.cert451.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry225_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry225_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights451_linked j (List.mem_finRange j))
theorem actual_frozen_frame225 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame225 (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.flow.timeParameter_mem child_geometry225_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights225 hz)
theorem r_profile226_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r226=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds := by rfl
theorem a_profile226_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a226=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a226.bounds := by rfl
theorem r_fixed226_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 7 := by decide +kernel
theorem a_fixed226_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a226.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.a226.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 9 := by decide +kernel
theorem ranks226_linked : ReferenceRankData.CoarseLowerShape.Batch0028.targetR226=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0028.targetA226=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 1 := by decide +kernel
theorem r_input226_linked : ReferenceRankData.CoarseLowerShape.Batch0028.r226.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds.gauge] := by decide +kernel
theorem a_input226_linked : ReferenceRankData.CoarseLowerShape.Batch0028.a226.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.a226.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.a226.bounds.gauge] := by decide +kernel
theorem geometry226_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.a := by decide +kernel
theorem weights452_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0056.cert452.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights453_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0056.cert453.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time226_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 10)=true := by decide +kernel
theorem r_reference226_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 0)=true := by decide +kernel
theorem a_reference226_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 1)=true := by decide +kernel
theorem rank_r_link226_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r226 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link226_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0028.a226.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a226 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints226 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell true ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r226 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile226_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link226_checked
    geometry226_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell false ReferenceProfileData.CoarseLowerShape.Batch0028.a226.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a226 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile226_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link226_checked
    geometry226_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks226_linked.1,←ranks226_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0028.r226.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a226.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0028.ordered226_checked hr ha ho
theorem frozen_frame226 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226 ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds ReferenceProfileData.CoarseLowerShape.Batch0028.a226.bounds
  · rw [←r_profile226_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile226_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry226_linked.2.2.2.2.1
  · exact geometry226_linked.2.2.2.2.2
  · exact r_reference226_checked
  · exact a_reference226_checked
  · exact r_fixed226_linked
  · exact a_fixed226_linked
  · exact time226_checked
  · exact ht
  · exact hw
theorem child_geometry226_checked : ReferenceWeightData.CoarseLowerShape.Batch0056.cert452.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0056.cert452.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0056.cert453.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0056.cert453.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights226 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0056.cert452∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch56_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0056.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0056.cert453∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch56_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0056.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0056.cert452.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0056.cert452.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0056.cert452.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry226_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights452_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0056.cert453.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0056.cert453.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry226_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry226_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights453_linked j (List.mem_finRange j))
theorem actual_frozen_frame226 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame226 (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.flow.timeParameter_mem child_geometry226_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights226 hz)
theorem r_profile227_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r227=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds := by rfl
theorem a_profile227_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a227=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a227.bounds := by rfl
theorem r_fixed227_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 7 := by decide +kernel
theorem a_fixed227_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a227.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.a227.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 9 := by decide +kernel
theorem ranks227_linked : ReferenceRankData.CoarseLowerShape.Batch0028.targetR227=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0028.targetA227=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 1 := by decide +kernel
theorem r_input227_linked : ReferenceRankData.CoarseLowerShape.Batch0028.r227.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds.gauge] := by decide +kernel
theorem a_input227_linked : ReferenceRankData.CoarseLowerShape.Batch0028.a227.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.a227.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.a227.bounds.gauge] := by decide +kernel
theorem geometry227_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.a := by decide +kernel
theorem weights454_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0056.cert454.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights455_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0056.cert455.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time227_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 10)=true := by decide +kernel
theorem r_reference227_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 0)=true := by decide +kernel
theorem a_reference227_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 1)=true := by decide +kernel
theorem rank_r_link227_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r227 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link227_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0028.a227.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a227 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints227 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell true ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r227 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile227_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link227_checked
    geometry227_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell false ReferenceProfileData.CoarseLowerShape.Batch0028.a227.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a227 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile227_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link227_checked
    geometry227_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks227_linked.1,←ranks227_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0028.r227.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a227.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0028.ordered227_checked hr ha ho
theorem frozen_frame227 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227 ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds ReferenceProfileData.CoarseLowerShape.Batch0028.a227.bounds
  · rw [←r_profile227_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile227_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry227_linked.2.2.2.2.1
  · exact geometry227_linked.2.2.2.2.2
  · exact r_reference227_checked
  · exact a_reference227_checked
  · exact r_fixed227_linked
  · exact a_fixed227_linked
  · exact time227_checked
  · exact ht
  · exact hw
theorem child_geometry227_checked : ReferenceWeightData.CoarseLowerShape.Batch0056.cert454.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0056.cert454.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0056.cert455.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0056.cert455.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights227 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0056.cert454∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch56_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0056.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0056.cert455∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch56_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0056.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0056.cert454.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0056.cert454.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0056.cert454.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry227_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights454_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0056.cert455.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0056.cert455.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry227_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry227_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights455_linked j (List.mem_finRange j))
theorem actual_frozen_frame227 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame227 (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.flow.timeParameter_mem child_geometry227_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights227 hz)
theorem r_profile228_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r228=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds := by rfl
theorem a_profile228_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a228=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a228.bounds := by rfl
theorem r_fixed228_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 7 := by decide +kernel
theorem a_fixed228_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a228.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.a228.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 9 := by decide +kernel
theorem ranks228_linked : ReferenceRankData.CoarseLowerShape.Batch0028.targetR228=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0028.targetA228=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 1 := by decide +kernel
theorem r_input228_linked : ReferenceRankData.CoarseLowerShape.Batch0028.r228.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds.gauge] := by decide +kernel
theorem a_input228_linked : ReferenceRankData.CoarseLowerShape.Batch0028.a228.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.a228.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.a228.bounds.gauge] := by decide +kernel
theorem geometry228_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.a := by decide +kernel
theorem weights456_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0057.cert456.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights457_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0057.cert457.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time228_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 10)=true := by decide +kernel
theorem r_reference228_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 0)=true := by decide +kernel
theorem a_reference228_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 1)=true := by decide +kernel
theorem rank_r_link228_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r228 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link228_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0028.a228.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a228 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints228 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell true ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r228 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile228_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link228_checked
    geometry228_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell false ReferenceProfileData.CoarseLowerShape.Batch0028.a228.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a228 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile228_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link228_checked
    geometry228_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks228_linked.1,←ranks228_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0028.r228.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a228.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0028.ordered228_checked hr ha ho
theorem frozen_frame228 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228 ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds ReferenceProfileData.CoarseLowerShape.Batch0028.a228.bounds
  · rw [←r_profile228_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile228_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry228_linked.2.2.2.2.1
  · exact geometry228_linked.2.2.2.2.2
  · exact r_reference228_checked
  · exact a_reference228_checked
  · exact r_fixed228_linked
  · exact a_fixed228_linked
  · exact time228_checked
  · exact ht
  · exact hw
theorem child_geometry228_checked : ReferenceWeightData.CoarseLowerShape.Batch0057.cert456.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0057.cert456.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0057.cert457.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0057.cert457.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights228 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0057.cert456∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch57_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0057.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0057.cert457∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch57_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0057.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0057.cert456.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0057.cert456.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0057.cert456.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry228_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights456_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0057.cert457.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0057.cert457.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry228_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry228_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights457_linked j (List.mem_finRange j))
theorem actual_frozen_frame228 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame228 (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.flow.timeParameter_mem child_geometry228_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights228 hz)
theorem r_profile229_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r229=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds := by rfl
theorem a_profile229_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a229=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a229.bounds := by rfl
theorem r_fixed229_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 7 := by decide +kernel
theorem a_fixed229_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a229.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.a229.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 9 := by decide +kernel
theorem ranks229_linked : ReferenceRankData.CoarseLowerShape.Batch0028.targetR229=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0028.targetA229=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 1 := by decide +kernel
theorem r_input229_linked : ReferenceRankData.CoarseLowerShape.Batch0028.r229.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds.gauge] := by decide +kernel
theorem a_input229_linked : ReferenceRankData.CoarseLowerShape.Batch0028.a229.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.a229.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.a229.bounds.gauge] := by decide +kernel
theorem geometry229_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.a := by decide +kernel
theorem weights458_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0057.cert458.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights459_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0057.cert459.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time229_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 10)=true := by decide +kernel
theorem r_reference229_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 0)=true := by decide +kernel
theorem a_reference229_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 1)=true := by decide +kernel
theorem rank_r_link229_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r229 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link229_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0028.a229.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a229 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints229 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell true ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r229 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile229_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link229_checked
    geometry229_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell false ReferenceProfileData.CoarseLowerShape.Batch0028.a229.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a229 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile229_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link229_checked
    geometry229_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks229_linked.1,←ranks229_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0028.r229.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a229.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0028.ordered229_checked hr ha ho
theorem frozen_frame229 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229 ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds ReferenceProfileData.CoarseLowerShape.Batch0028.a229.bounds
  · rw [←r_profile229_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile229_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry229_linked.2.2.2.2.1
  · exact geometry229_linked.2.2.2.2.2
  · exact r_reference229_checked
  · exact a_reference229_checked
  · exact r_fixed229_linked
  · exact a_fixed229_linked
  · exact time229_checked
  · exact ht
  · exact hw
theorem child_geometry229_checked : ReferenceWeightData.CoarseLowerShape.Batch0057.cert458.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0057.cert458.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0057.cert459.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0057.cert459.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights229 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0057.cert458∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch57_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0057.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0057.cert459∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch57_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0057.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0057.cert458.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0057.cert458.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0057.cert458.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry229_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights458_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0057.cert459.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0057.cert459.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry229_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry229_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights459_linked j (List.mem_finRange j))
theorem actual_frozen_frame229 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame229 (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.flow.timeParameter_mem child_geometry229_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights229 hz)
theorem r_profile230_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r230=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds := by rfl
theorem a_profile230_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a230=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a230.bounds := by rfl
theorem r_fixed230_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 7 := by decide +kernel
theorem a_fixed230_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a230.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.a230.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 9 := by decide +kernel
theorem ranks230_linked : ReferenceRankData.CoarseLowerShape.Batch0028.targetR230=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0028.targetA230=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 1 := by decide +kernel
theorem r_input230_linked : ReferenceRankData.CoarseLowerShape.Batch0028.r230.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds.gauge] := by decide +kernel
theorem a_input230_linked : ReferenceRankData.CoarseLowerShape.Batch0028.a230.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.a230.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.a230.bounds.gauge] := by decide +kernel
theorem geometry230_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.a := by decide +kernel
theorem weights460_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0057.cert460.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights461_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0057.cert461.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time230_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 10)=true := by decide +kernel
theorem r_reference230_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 0)=true := by decide +kernel
theorem a_reference230_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 1)=true := by decide +kernel
theorem rank_r_link230_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r230 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link230_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0028.a230.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a230 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints230 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell true ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r230 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile230_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link230_checked
    geometry230_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell false ReferenceProfileData.CoarseLowerShape.Batch0028.a230.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a230 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile230_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link230_checked
    geometry230_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks230_linked.1,←ranks230_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0028.r230.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a230.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0028.ordered230_checked hr ha ho
theorem frozen_frame230 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230 ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds ReferenceProfileData.CoarseLowerShape.Batch0028.a230.bounds
  · rw [←r_profile230_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile230_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry230_linked.2.2.2.2.1
  · exact geometry230_linked.2.2.2.2.2
  · exact r_reference230_checked
  · exact a_reference230_checked
  · exact r_fixed230_linked
  · exact a_fixed230_linked
  · exact time230_checked
  · exact ht
  · exact hw
theorem child_geometry230_checked : ReferenceWeightData.CoarseLowerShape.Batch0057.cert460.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0057.cert460.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0057.cert461.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0057.cert461.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights230 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0057.cert460∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch57_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0057.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0057.cert461∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch57_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0057.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0057.cert460.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0057.cert460.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0057.cert460.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry230_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights460_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0057.cert461.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0057.cert461.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry230_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry230_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights461_linked j (List.mem_finRange j))
theorem actual_frozen_frame230 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame230 (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.flow.timeParameter_mem child_geometry230_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights230 hz)
theorem r_profile231_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r231=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds := by rfl
theorem a_profile231_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a231=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a231.bounds := by rfl
theorem r_fixed231_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 7 := by decide +kernel
theorem a_fixed231_linked : ReferenceProfileData.CoarseLowerShape.Batch0028.a231.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0028.a231.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 9 := by decide +kernel
theorem ranks231_linked : ReferenceRankData.CoarseLowerShape.Batch0028.targetR231=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0028.targetA231=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 1 := by decide +kernel
theorem r_input231_linked : ReferenceRankData.CoarseLowerShape.Batch0028.r231.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds.gauge] := by decide +kernel
theorem a_input231_linked : ReferenceRankData.CoarseLowerShape.Batch0028.a231.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0028.a231.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0028.a231.bounds.gauge] := by decide +kernel
theorem geometry231_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.a := by decide +kernel
theorem weights462_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0057.cert462.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights463_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0057.cert463.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time231_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 10)=true := by decide +kernel
theorem r_reference231_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 0)=true := by decide +kernel
theorem a_reference231_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 1)=true := by decide +kernel
theorem rank_r_link231_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r231 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link231_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0028.a231.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a231 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints231 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell true ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds ReferenceRankData.CoarseLowerShape.Batch0028.r231 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile231_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link231_checked
    geometry231_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell false ReferenceProfileData.CoarseLowerShape.Batch0028.a231.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a231 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile231_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0028.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0028.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link231_checked
    geometry231_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks231_linked.1,←ranks231_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0028.r231.bounds ReferenceRankData.CoarseLowerShape.Batch0028.a231.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0028.ordered231_checked hr ha ho
theorem frozen_frame231 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231 ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds ReferenceProfileData.CoarseLowerShape.Batch0028.a231.bounds
  · rw [←r_profile231_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile231_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry231_linked.2.2.2.2.1
  · exact geometry231_linked.2.2.2.2.2
  · exact r_reference231_checked
  · exact a_reference231_checked
  · exact r_fixed231_linked
  · exact a_fixed231_linked
  · exact time231_checked
  · exact ht
  · exact hw
theorem child_geometry231_checked : ReferenceWeightData.CoarseLowerShape.Batch0057.cert462.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0057.cert462.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0057.cert463.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0057.cert463.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights231 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0057.cert462∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch57_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0057.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0057.cert463∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch57_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0057.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0057.cert462.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0057.cert462.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0057.cert462.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry231_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights462_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0057.cert463.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0057.cert463.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry231_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry231_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights463_linked j (List.mem_finRange j))
theorem actual_frozen_frame231 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame231 (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.flow.timeParameter_mem child_geometry231_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights231 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell224),(ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell225),(ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell226),(ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell227),(ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell228),(ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell229),(ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell230),(ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0028.cell231)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0028.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0028.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame224 hz
  · exact fun z hz=>actual_frozen_frame225 hz
  · exact fun z hz=>actual_frozen_frame226 hz
  · exact fun z hz=>actual_frozen_frame227 hz
  · exact fun z hz=>actual_frozen_frame228 hz
  · exact fun z hz=>actual_frozen_frame229 hz
  · exact fun z hz=>actual_frozen_frame230 hz
  · exact fun z hz=>actual_frozen_frame231 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints224 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints225 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints226 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints227 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints228 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints229 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints230 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints231 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry224_linked.1,geometry224_linked.2.1,geometry224_linked.2.2.1,geometry224_linked.2.2.2.1⟩
  · exact ⟨geometry225_linked.1,geometry225_linked.2.1,geometry225_linked.2.2.1,geometry225_linked.2.2.2.1⟩
  · exact ⟨geometry226_linked.1,geometry226_linked.2.1,geometry226_linked.2.2.1,geometry226_linked.2.2.2.1⟩
  · exact ⟨geometry227_linked.1,geometry227_linked.2.1,geometry227_linked.2.2.1,geometry227_linked.2.2.2.1⟩
  · exact ⟨geometry228_linked.1,geometry228_linked.2.1,geometry228_linked.2.2.1,geometry228_linked.2.2.2.1⟩
  · exact ⟨geometry229_linked.1,geometry229_linked.2.1,geometry229_linked.2.2.1,geometry229_linked.2.2.2.1⟩
  · exact ⟨geometry230_linked.1,geometry230_linked.2.1,geometry230_linked.2.2.1,geometry230_linked.2.2.2.1⟩
  · exact ⟨geometry231_linked.1,geometry231_linked.2.1,geometry231_linked.2.2.1,geometry231_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.a224.bounds,?_,geometry224_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a224.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile224_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds,?_,geometry224_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert224.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r224.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile224_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.a225.bounds,?_,geometry225_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a225.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile225_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds,?_,geometry225_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert225.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r225.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile225_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.a226.bounds,?_,geometry226_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a226.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile226_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds,?_,geometry226_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert226.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r226.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile226_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.a227.bounds,?_,geometry227_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a227.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile227_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds,?_,geometry227_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert227.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r227.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile227_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.a228.bounds,?_,geometry228_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a228.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile228_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds,?_,geometry228_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert228.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r228.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile228_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.a229.bounds,?_,geometry229_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a229.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile229_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds,?_,geometry229_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert229.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r229.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile229_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.a230.bounds,?_,geometry230_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a230.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile230_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds,?_,geometry230_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert230.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r230.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile230_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.a231.bounds,?_,geometry231_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0028.a231.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile231_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds,?_,geometry231_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0028.cert231.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0028.r231.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile231_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0028.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0028.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0028

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0029
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch58_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0058.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0058.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch59_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0059.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0059.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile232_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r232=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds := by rfl
theorem a_profile232_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a232=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a232.bounds := by rfl
theorem r_fixed232_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 7 := by decide +kernel
theorem a_fixed232_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a232.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.a232.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 9 := by decide +kernel
theorem ranks232_linked : ReferenceRankData.CoarseLowerShape.Batch0029.targetR232=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0029.targetA232=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 1 := by decide +kernel
theorem r_input232_linked : ReferenceRankData.CoarseLowerShape.Batch0029.r232.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds.gauge] := by decide +kernel
theorem a_input232_linked : ReferenceRankData.CoarseLowerShape.Batch0029.a232.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.a232.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.a232.bounds.gauge] := by decide +kernel
theorem geometry232_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.a := by decide +kernel
theorem weights464_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0058.cert464.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights465_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0058.cert465.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time232_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 10)=true := by decide +kernel
theorem r_reference232_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 0)=true := by decide +kernel
theorem a_reference232_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 1)=true := by decide +kernel
theorem rank_r_link232_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r232 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link232_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0029.a232.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a232 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints232 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell true ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r232 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile232_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link232_checked
    geometry232_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell false ReferenceProfileData.CoarseLowerShape.Batch0029.a232.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a232 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile232_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link232_checked
    geometry232_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks232_linked.1,←ranks232_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0029.r232.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a232.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0029.ordered232_checked hr ha ho
theorem frozen_frame232 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232 ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds ReferenceProfileData.CoarseLowerShape.Batch0029.a232.bounds
  · rw [←r_profile232_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile232_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry232_linked.2.2.2.2.1
  · exact geometry232_linked.2.2.2.2.2
  · exact r_reference232_checked
  · exact a_reference232_checked
  · exact r_fixed232_linked
  · exact a_fixed232_linked
  · exact time232_checked
  · exact ht
  · exact hw
theorem child_geometry232_checked : ReferenceWeightData.CoarseLowerShape.Batch0058.cert464.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0058.cert464.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0058.cert465.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0058.cert465.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights232 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0058.cert464∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch58_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0058.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0058.cert465∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch58_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0058.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0058.cert464.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0058.cert464.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0058.cert464.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry232_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights464_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0058.cert465.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0058.cert465.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry232_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry232_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights465_linked j (List.mem_finRange j))
theorem actual_frozen_frame232 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame232 (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.flow.timeParameter_mem child_geometry232_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights232 hz)
theorem r_profile233_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r233=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds := by rfl
theorem a_profile233_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a233=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a233.bounds := by rfl
theorem r_fixed233_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 7 := by decide +kernel
theorem a_fixed233_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a233.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.a233.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 9 := by decide +kernel
theorem ranks233_linked : ReferenceRankData.CoarseLowerShape.Batch0029.targetR233=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0029.targetA233=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 1 := by decide +kernel
theorem r_input233_linked : ReferenceRankData.CoarseLowerShape.Batch0029.r233.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds.gauge] := by decide +kernel
theorem a_input233_linked : ReferenceRankData.CoarseLowerShape.Batch0029.a233.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.a233.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.a233.bounds.gauge] := by decide +kernel
theorem geometry233_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.a := by decide +kernel
theorem weights466_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0058.cert466.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights467_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0058.cert467.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time233_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 10)=true := by decide +kernel
theorem r_reference233_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 0)=true := by decide +kernel
theorem a_reference233_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 1)=true := by decide +kernel
theorem rank_r_link233_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r233 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link233_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0029.a233.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a233 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints233 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell true ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r233 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile233_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link233_checked
    geometry233_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell false ReferenceProfileData.CoarseLowerShape.Batch0029.a233.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a233 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile233_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link233_checked
    geometry233_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks233_linked.1,←ranks233_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0029.r233.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a233.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0029.ordered233_checked hr ha ho
theorem frozen_frame233 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233 ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds ReferenceProfileData.CoarseLowerShape.Batch0029.a233.bounds
  · rw [←r_profile233_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile233_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry233_linked.2.2.2.2.1
  · exact geometry233_linked.2.2.2.2.2
  · exact r_reference233_checked
  · exact a_reference233_checked
  · exact r_fixed233_linked
  · exact a_fixed233_linked
  · exact time233_checked
  · exact ht
  · exact hw
theorem child_geometry233_checked : ReferenceWeightData.CoarseLowerShape.Batch0058.cert466.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0058.cert466.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0058.cert467.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0058.cert467.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights233 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0058.cert466∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch58_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0058.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0058.cert467∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch58_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0058.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0058.cert466.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0058.cert466.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0058.cert466.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry233_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights466_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0058.cert467.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0058.cert467.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry233_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry233_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights467_linked j (List.mem_finRange j))
theorem actual_frozen_frame233 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame233 (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.flow.timeParameter_mem child_geometry233_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights233 hz)
theorem r_profile234_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r234=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds := by rfl
theorem a_profile234_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a234=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a234.bounds := by rfl
theorem r_fixed234_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 7 := by decide +kernel
theorem a_fixed234_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a234.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.a234.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 9 := by decide +kernel
theorem ranks234_linked : ReferenceRankData.CoarseLowerShape.Batch0029.targetR234=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0029.targetA234=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 1 := by decide +kernel
theorem r_input234_linked : ReferenceRankData.CoarseLowerShape.Batch0029.r234.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds.gauge] := by decide +kernel
theorem a_input234_linked : ReferenceRankData.CoarseLowerShape.Batch0029.a234.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.a234.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.a234.bounds.gauge] := by decide +kernel
theorem geometry234_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.a := by decide +kernel
theorem weights468_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0058.cert468.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights469_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0058.cert469.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time234_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 10)=true := by decide +kernel
theorem r_reference234_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 0)=true := by decide +kernel
theorem a_reference234_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 1)=true := by decide +kernel
theorem rank_r_link234_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r234 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link234_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0029.a234.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a234 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints234 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell true ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r234 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile234_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link234_checked
    geometry234_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell false ReferenceProfileData.CoarseLowerShape.Batch0029.a234.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a234 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile234_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link234_checked
    geometry234_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks234_linked.1,←ranks234_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0029.r234.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a234.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0029.ordered234_checked hr ha ho
theorem frozen_frame234 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234 ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds ReferenceProfileData.CoarseLowerShape.Batch0029.a234.bounds
  · rw [←r_profile234_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile234_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry234_linked.2.2.2.2.1
  · exact geometry234_linked.2.2.2.2.2
  · exact r_reference234_checked
  · exact a_reference234_checked
  · exact r_fixed234_linked
  · exact a_fixed234_linked
  · exact time234_checked
  · exact ht
  · exact hw
theorem child_geometry234_checked : ReferenceWeightData.CoarseLowerShape.Batch0058.cert468.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0058.cert468.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0058.cert469.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0058.cert469.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights234 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0058.cert468∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch58_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0058.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0058.cert469∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch58_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0058.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0058.cert468.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0058.cert468.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0058.cert468.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry234_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights468_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0058.cert469.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0058.cert469.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry234_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry234_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights469_linked j (List.mem_finRange j))
theorem actual_frozen_frame234 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame234 (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.flow.timeParameter_mem child_geometry234_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights234 hz)
theorem r_profile235_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r235=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds := by rfl
theorem a_profile235_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a235=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a235.bounds := by rfl
theorem r_fixed235_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 7 := by decide +kernel
theorem a_fixed235_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a235.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.a235.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 9 := by decide +kernel
theorem ranks235_linked : ReferenceRankData.CoarseLowerShape.Batch0029.targetR235=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0029.targetA235=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 1 := by decide +kernel
theorem r_input235_linked : ReferenceRankData.CoarseLowerShape.Batch0029.r235.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds.gauge] := by decide +kernel
theorem a_input235_linked : ReferenceRankData.CoarseLowerShape.Batch0029.a235.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.a235.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.a235.bounds.gauge] := by decide +kernel
theorem geometry235_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.a := by decide +kernel
theorem weights470_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0058.cert470.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights471_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0058.cert471.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time235_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 10)=true := by decide +kernel
theorem r_reference235_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 0)=true := by decide +kernel
theorem a_reference235_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 1)=true := by decide +kernel
theorem rank_r_link235_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r235 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link235_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0029.a235.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a235 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints235 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell true ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r235 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile235_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link235_checked
    geometry235_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell false ReferenceProfileData.CoarseLowerShape.Batch0029.a235.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a235 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile235_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link235_checked
    geometry235_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks235_linked.1,←ranks235_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0029.r235.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a235.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0029.ordered235_checked hr ha ho
theorem frozen_frame235 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235 ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds ReferenceProfileData.CoarseLowerShape.Batch0029.a235.bounds
  · rw [←r_profile235_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile235_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry235_linked.2.2.2.2.1
  · exact geometry235_linked.2.2.2.2.2
  · exact r_reference235_checked
  · exact a_reference235_checked
  · exact r_fixed235_linked
  · exact a_fixed235_linked
  · exact time235_checked
  · exact ht
  · exact hw
theorem child_geometry235_checked : ReferenceWeightData.CoarseLowerShape.Batch0058.cert470.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0058.cert470.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0058.cert471.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0058.cert471.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights235 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0058.cert470∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch58_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0058.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0058.cert471∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch58_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0058.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0058.cert470.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0058.cert470.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0058.cert470.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry235_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights470_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0058.cert471.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0058.cert471.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry235_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry235_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights471_linked j (List.mem_finRange j))
theorem actual_frozen_frame235 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame235 (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.flow.timeParameter_mem child_geometry235_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights235 hz)
theorem r_profile236_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r236=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds := by rfl
theorem a_profile236_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a236=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a236.bounds := by rfl
theorem r_fixed236_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 7 := by decide +kernel
theorem a_fixed236_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a236.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.a236.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 9 := by decide +kernel
theorem ranks236_linked : ReferenceRankData.CoarseLowerShape.Batch0029.targetR236=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0029.targetA236=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 1 := by decide +kernel
theorem r_input236_linked : ReferenceRankData.CoarseLowerShape.Batch0029.r236.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds.gauge] := by decide +kernel
theorem a_input236_linked : ReferenceRankData.CoarseLowerShape.Batch0029.a236.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.a236.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.a236.bounds.gauge] := by decide +kernel
theorem geometry236_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.a := by decide +kernel
theorem weights472_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0059.cert472.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights473_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0059.cert473.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time236_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 10)=true := by decide +kernel
theorem r_reference236_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 0)=true := by decide +kernel
theorem a_reference236_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 1)=true := by decide +kernel
theorem rank_r_link236_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r236 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link236_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0029.a236.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a236 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints236 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell true ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r236 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile236_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link236_checked
    geometry236_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell false ReferenceProfileData.CoarseLowerShape.Batch0029.a236.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a236 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile236_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link236_checked
    geometry236_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks236_linked.1,←ranks236_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0029.r236.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a236.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0029.ordered236_checked hr ha ho
theorem frozen_frame236 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236 ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds ReferenceProfileData.CoarseLowerShape.Batch0029.a236.bounds
  · rw [←r_profile236_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile236_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry236_linked.2.2.2.2.1
  · exact geometry236_linked.2.2.2.2.2
  · exact r_reference236_checked
  · exact a_reference236_checked
  · exact r_fixed236_linked
  · exact a_fixed236_linked
  · exact time236_checked
  · exact ht
  · exact hw
theorem child_geometry236_checked : ReferenceWeightData.CoarseLowerShape.Batch0059.cert472.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0059.cert472.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0059.cert473.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0059.cert473.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights236 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0059.cert472∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch59_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0059.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0059.cert473∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch59_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0059.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0059.cert472.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0059.cert472.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0059.cert472.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry236_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights472_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0059.cert473.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0059.cert473.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry236_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry236_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights473_linked j (List.mem_finRange j))
theorem actual_frozen_frame236 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame236 (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.flow.timeParameter_mem child_geometry236_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights236 hz)
theorem r_profile237_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r237=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds := by rfl
theorem a_profile237_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a237=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a237.bounds := by rfl
theorem r_fixed237_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 7 := by decide +kernel
theorem a_fixed237_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a237.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.a237.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 9 := by decide +kernel
theorem ranks237_linked : ReferenceRankData.CoarseLowerShape.Batch0029.targetR237=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0029.targetA237=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 1 := by decide +kernel
theorem r_input237_linked : ReferenceRankData.CoarseLowerShape.Batch0029.r237.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds.gauge] := by decide +kernel
theorem a_input237_linked : ReferenceRankData.CoarseLowerShape.Batch0029.a237.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.a237.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.a237.bounds.gauge] := by decide +kernel
theorem geometry237_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.a := by decide +kernel
theorem weights474_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0059.cert474.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights475_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0059.cert475.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time237_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 10)=true := by decide +kernel
theorem r_reference237_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 0)=true := by decide +kernel
theorem a_reference237_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 1)=true := by decide +kernel
theorem rank_r_link237_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r237 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link237_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0029.a237.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a237 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints237 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell true ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r237 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile237_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link237_checked
    geometry237_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell false ReferenceProfileData.CoarseLowerShape.Batch0029.a237.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a237 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile237_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link237_checked
    geometry237_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks237_linked.1,←ranks237_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0029.r237.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a237.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0029.ordered237_checked hr ha ho
theorem frozen_frame237 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237 ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds ReferenceProfileData.CoarseLowerShape.Batch0029.a237.bounds
  · rw [←r_profile237_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile237_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry237_linked.2.2.2.2.1
  · exact geometry237_linked.2.2.2.2.2
  · exact r_reference237_checked
  · exact a_reference237_checked
  · exact r_fixed237_linked
  · exact a_fixed237_linked
  · exact time237_checked
  · exact ht
  · exact hw
theorem child_geometry237_checked : ReferenceWeightData.CoarseLowerShape.Batch0059.cert474.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0059.cert474.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0059.cert475.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0059.cert475.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights237 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0059.cert474∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch59_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0059.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0059.cert475∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch59_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0059.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0059.cert474.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0059.cert474.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0059.cert474.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry237_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights474_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0059.cert475.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0059.cert475.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry237_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry237_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights475_linked j (List.mem_finRange j))
theorem actual_frozen_frame237 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame237 (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.flow.timeParameter_mem child_geometry237_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights237 hz)
theorem r_profile238_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r238=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds := by rfl
theorem a_profile238_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a238=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a238.bounds := by rfl
theorem r_fixed238_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 7 := by decide +kernel
theorem a_fixed238_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a238.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.a238.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 9 := by decide +kernel
theorem ranks238_linked : ReferenceRankData.CoarseLowerShape.Batch0029.targetR238=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0029.targetA238=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 1 := by decide +kernel
theorem r_input238_linked : ReferenceRankData.CoarseLowerShape.Batch0029.r238.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds.gauge] := by decide +kernel
theorem a_input238_linked : ReferenceRankData.CoarseLowerShape.Batch0029.a238.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.a238.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.a238.bounds.gauge] := by decide +kernel
theorem geometry238_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.a := by decide +kernel
theorem weights476_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0059.cert476.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights477_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0059.cert477.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time238_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 10)=true := by decide +kernel
theorem r_reference238_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 0)=true := by decide +kernel
theorem a_reference238_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 1)=true := by decide +kernel
theorem rank_r_link238_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r238 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link238_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0029.a238.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a238 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints238 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell true ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r238 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile238_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link238_checked
    geometry238_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell false ReferenceProfileData.CoarseLowerShape.Batch0029.a238.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a238 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile238_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link238_checked
    geometry238_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks238_linked.1,←ranks238_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0029.r238.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a238.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0029.ordered238_checked hr ha ho
theorem frozen_frame238 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238 ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds ReferenceProfileData.CoarseLowerShape.Batch0029.a238.bounds
  · rw [←r_profile238_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile238_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry238_linked.2.2.2.2.1
  · exact geometry238_linked.2.2.2.2.2
  · exact r_reference238_checked
  · exact a_reference238_checked
  · exact r_fixed238_linked
  · exact a_fixed238_linked
  · exact time238_checked
  · exact ht
  · exact hw
theorem child_geometry238_checked : ReferenceWeightData.CoarseLowerShape.Batch0059.cert476.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0059.cert476.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0059.cert477.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0059.cert477.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights238 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0059.cert476∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch59_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0059.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0059.cert477∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch59_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0059.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0059.cert476.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0059.cert476.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0059.cert476.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry238_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights476_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0059.cert477.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0059.cert477.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry238_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry238_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights477_linked j (List.mem_finRange j))
theorem actual_frozen_frame238 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame238 (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.flow.timeParameter_mem child_geometry238_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights238 hz)
theorem r_profile239_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r239=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds := by rfl
theorem a_profile239_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a239=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a239.bounds := by rfl
theorem r_fixed239_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 7 := by decide +kernel
theorem a_fixed239_linked : ReferenceProfileData.CoarseLowerShape.Batch0029.a239.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0029.a239.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 9 := by decide +kernel
theorem ranks239_linked : ReferenceRankData.CoarseLowerShape.Batch0029.targetR239=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0029.targetA239=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 1 := by decide +kernel
theorem r_input239_linked : ReferenceRankData.CoarseLowerShape.Batch0029.r239.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds.gauge] := by decide +kernel
theorem a_input239_linked : ReferenceRankData.CoarseLowerShape.Batch0029.a239.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0029.a239.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0029.a239.bounds.gauge] := by decide +kernel
theorem geometry239_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.a := by decide +kernel
theorem weights478_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0059.cert478.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights479_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0059.cert479.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time239_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 10)=true := by decide +kernel
theorem r_reference239_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 0)=true := by decide +kernel
theorem a_reference239_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 1)=true := by decide +kernel
theorem rank_r_link239_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r239 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link239_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0029.a239.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a239 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints239 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell true ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds ReferenceRankData.CoarseLowerShape.Batch0029.r239 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile239_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link239_checked
    geometry239_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell false ReferenceProfileData.CoarseLowerShape.Batch0029.a239.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a239 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile239_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0029.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0029.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link239_checked
    geometry239_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks239_linked.1,←ranks239_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0029.r239.bounds ReferenceRankData.CoarseLowerShape.Batch0029.a239.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0029.ordered239_checked hr ha ho
theorem frozen_frame239 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239 ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds ReferenceProfileData.CoarseLowerShape.Batch0029.a239.bounds
  · rw [←r_profile239_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile239_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry239_linked.2.2.2.2.1
  · exact geometry239_linked.2.2.2.2.2
  · exact r_reference239_checked
  · exact a_reference239_checked
  · exact r_fixed239_linked
  · exact a_fixed239_linked
  · exact time239_checked
  · exact ht
  · exact hw
theorem child_geometry239_checked : ReferenceWeightData.CoarseLowerShape.Batch0059.cert478.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0059.cert478.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0059.cert479.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0059.cert479.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights239 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0059.cert478∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch59_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0059.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0059.cert479∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch59_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0059.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0059.cert478.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0059.cert478.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0059.cert478.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry239_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights478_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0059.cert479.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0059.cert479.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry239_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry239_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights479_linked j (List.mem_finRange j))
theorem actual_frozen_frame239 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame239 (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.flow.timeParameter_mem child_geometry239_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights239 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell232),(ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell233),(ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell234),(ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell235),(ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell236),(ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell237),(ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell238),(ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0029.cell239)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0029.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0029.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame232 hz
  · exact fun z hz=>actual_frozen_frame233 hz
  · exact fun z hz=>actual_frozen_frame234 hz
  · exact fun z hz=>actual_frozen_frame235 hz
  · exact fun z hz=>actual_frozen_frame236 hz
  · exact fun z hz=>actual_frozen_frame237 hz
  · exact fun z hz=>actual_frozen_frame238 hz
  · exact fun z hz=>actual_frozen_frame239 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints232 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints233 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints234 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints235 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints236 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints237 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints238 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints239 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry232_linked.1,geometry232_linked.2.1,geometry232_linked.2.2.1,geometry232_linked.2.2.2.1⟩
  · exact ⟨geometry233_linked.1,geometry233_linked.2.1,geometry233_linked.2.2.1,geometry233_linked.2.2.2.1⟩
  · exact ⟨geometry234_linked.1,geometry234_linked.2.1,geometry234_linked.2.2.1,geometry234_linked.2.2.2.1⟩
  · exact ⟨geometry235_linked.1,geometry235_linked.2.1,geometry235_linked.2.2.1,geometry235_linked.2.2.2.1⟩
  · exact ⟨geometry236_linked.1,geometry236_linked.2.1,geometry236_linked.2.2.1,geometry236_linked.2.2.2.1⟩
  · exact ⟨geometry237_linked.1,geometry237_linked.2.1,geometry237_linked.2.2.1,geometry237_linked.2.2.2.1⟩
  · exact ⟨geometry238_linked.1,geometry238_linked.2.1,geometry238_linked.2.2.1,geometry238_linked.2.2.2.1⟩
  · exact ⟨geometry239_linked.1,geometry239_linked.2.1,geometry239_linked.2.2.1,geometry239_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.a232.bounds,?_,geometry232_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a232.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile232_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds,?_,geometry232_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert232.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r232.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile232_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.a233.bounds,?_,geometry233_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a233.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile233_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds,?_,geometry233_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert233.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r233.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile233_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.a234.bounds,?_,geometry234_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a234.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile234_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds,?_,geometry234_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert234.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r234.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile234_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.a235.bounds,?_,geometry235_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a235.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile235_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds,?_,geometry235_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert235.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r235.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile235_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.a236.bounds,?_,geometry236_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a236.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile236_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds,?_,geometry236_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert236.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r236.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile236_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.a237.bounds,?_,geometry237_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a237.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile237_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds,?_,geometry237_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert237.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r237.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile237_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.a238.bounds,?_,geometry238_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a238.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile238_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds,?_,geometry238_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert238.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r238.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile238_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.a239.bounds,?_,geometry239_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0029.a239.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile239_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds,?_,geometry239_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0029.cert239.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0029.r239.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile239_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0029.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0029.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0029

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0030
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch60_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0060.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0060.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch61_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0061.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0061.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile240_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r240=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds := by rfl
theorem a_profile240_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a240=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a240.bounds := by rfl
theorem r_fixed240_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 7 := by decide +kernel
theorem a_fixed240_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a240.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.a240.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 9 := by decide +kernel
theorem ranks240_linked : ReferenceRankData.CoarseLowerShape.Batch0030.targetR240=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0030.targetA240=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 1 := by decide +kernel
theorem r_input240_linked : ReferenceRankData.CoarseLowerShape.Batch0030.r240.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds.gauge] := by decide +kernel
theorem a_input240_linked : ReferenceRankData.CoarseLowerShape.Batch0030.a240.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.a240.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.a240.bounds.gauge] := by decide +kernel
theorem geometry240_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.a := by decide +kernel
theorem weights480_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0060.cert480.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights481_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0060.cert481.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time240_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 10)=true := by decide +kernel
theorem r_reference240_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 0)=true := by decide +kernel
theorem a_reference240_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 1)=true := by decide +kernel
theorem rank_r_link240_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r240 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link240_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0030.a240.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a240 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints240 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell true ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r240 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile240_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link240_checked
    geometry240_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell false ReferenceProfileData.CoarseLowerShape.Batch0030.a240.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a240 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile240_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link240_checked
    geometry240_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks240_linked.1,←ranks240_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0030.r240.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a240.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0030.ordered240_checked hr ha ho
theorem frozen_frame240 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240 ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds ReferenceProfileData.CoarseLowerShape.Batch0030.a240.bounds
  · rw [←r_profile240_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile240_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry240_linked.2.2.2.2.1
  · exact geometry240_linked.2.2.2.2.2
  · exact r_reference240_checked
  · exact a_reference240_checked
  · exact r_fixed240_linked
  · exact a_fixed240_linked
  · exact time240_checked
  · exact ht
  · exact hw
theorem child_geometry240_checked : ReferenceWeightData.CoarseLowerShape.Batch0060.cert480.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0060.cert480.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0060.cert481.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0060.cert481.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights240 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0060.cert480∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch60_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0060.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0060.cert481∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch60_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0060.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0060.cert480.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0060.cert480.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0060.cert480.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry240_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights480_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0060.cert481.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0060.cert481.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry240_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry240_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights481_linked j (List.mem_finRange j))
theorem actual_frozen_frame240 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame240 (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.flow.timeParameter_mem child_geometry240_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights240 hz)
theorem r_profile241_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r241=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds := by rfl
theorem a_profile241_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a241=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a241.bounds := by rfl
theorem r_fixed241_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 7 := by decide +kernel
theorem a_fixed241_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a241.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.a241.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 9 := by decide +kernel
theorem ranks241_linked : ReferenceRankData.CoarseLowerShape.Batch0030.targetR241=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0030.targetA241=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 1 := by decide +kernel
theorem r_input241_linked : ReferenceRankData.CoarseLowerShape.Batch0030.r241.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds.gauge] := by decide +kernel
theorem a_input241_linked : ReferenceRankData.CoarseLowerShape.Batch0030.a241.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.a241.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.a241.bounds.gauge] := by decide +kernel
theorem geometry241_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.a := by decide +kernel
theorem weights482_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0060.cert482.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights483_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0060.cert483.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time241_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 10)=true := by decide +kernel
theorem r_reference241_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 0)=true := by decide +kernel
theorem a_reference241_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 1)=true := by decide +kernel
theorem rank_r_link241_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r241 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link241_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0030.a241.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a241 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints241 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell true ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r241 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile241_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link241_checked
    geometry241_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell false ReferenceProfileData.CoarseLowerShape.Batch0030.a241.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a241 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile241_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link241_checked
    geometry241_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks241_linked.1,←ranks241_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0030.r241.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a241.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0030.ordered241_checked hr ha ho
theorem frozen_frame241 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241 ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds ReferenceProfileData.CoarseLowerShape.Batch0030.a241.bounds
  · rw [←r_profile241_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile241_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry241_linked.2.2.2.2.1
  · exact geometry241_linked.2.2.2.2.2
  · exact r_reference241_checked
  · exact a_reference241_checked
  · exact r_fixed241_linked
  · exact a_fixed241_linked
  · exact time241_checked
  · exact ht
  · exact hw
theorem child_geometry241_checked : ReferenceWeightData.CoarseLowerShape.Batch0060.cert482.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0060.cert482.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0060.cert483.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0060.cert483.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights241 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0060.cert482∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch60_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0060.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0060.cert483∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch60_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0060.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0060.cert482.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0060.cert482.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0060.cert482.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry241_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights482_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0060.cert483.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0060.cert483.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry241_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry241_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights483_linked j (List.mem_finRange j))
theorem actual_frozen_frame241 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame241 (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.flow.timeParameter_mem child_geometry241_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights241 hz)
theorem r_profile242_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r242=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds := by rfl
theorem a_profile242_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a242=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a242.bounds := by rfl
theorem r_fixed242_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 7 := by decide +kernel
theorem a_fixed242_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a242.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.a242.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 9 := by decide +kernel
theorem ranks242_linked : ReferenceRankData.CoarseLowerShape.Batch0030.targetR242=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0030.targetA242=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 1 := by decide +kernel
theorem r_input242_linked : ReferenceRankData.CoarseLowerShape.Batch0030.r242.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds.gauge] := by decide +kernel
theorem a_input242_linked : ReferenceRankData.CoarseLowerShape.Batch0030.a242.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.a242.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.a242.bounds.gauge] := by decide +kernel
theorem geometry242_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.a := by decide +kernel
theorem weights484_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0060.cert484.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights485_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0060.cert485.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time242_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 10)=true := by decide +kernel
theorem r_reference242_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 0)=true := by decide +kernel
theorem a_reference242_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 1)=true := by decide +kernel
theorem rank_r_link242_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r242 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link242_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0030.a242.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a242 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints242 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell true ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r242 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile242_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link242_checked
    geometry242_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell false ReferenceProfileData.CoarseLowerShape.Batch0030.a242.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a242 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile242_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link242_checked
    geometry242_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks242_linked.1,←ranks242_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0030.r242.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a242.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0030.ordered242_checked hr ha ho
theorem frozen_frame242 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242 ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds ReferenceProfileData.CoarseLowerShape.Batch0030.a242.bounds
  · rw [←r_profile242_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile242_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry242_linked.2.2.2.2.1
  · exact geometry242_linked.2.2.2.2.2
  · exact r_reference242_checked
  · exact a_reference242_checked
  · exact r_fixed242_linked
  · exact a_fixed242_linked
  · exact time242_checked
  · exact ht
  · exact hw
theorem child_geometry242_checked : ReferenceWeightData.CoarseLowerShape.Batch0060.cert484.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0060.cert484.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0060.cert485.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0060.cert485.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights242 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0060.cert484∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch60_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0060.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0060.cert485∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch60_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0060.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0060.cert484.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0060.cert484.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0060.cert484.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry242_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights484_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0060.cert485.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0060.cert485.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry242_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry242_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights485_linked j (List.mem_finRange j))
theorem actual_frozen_frame242 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame242 (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.flow.timeParameter_mem child_geometry242_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights242 hz)
theorem r_profile243_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r243=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds := by rfl
theorem a_profile243_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a243=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a243.bounds := by rfl
theorem r_fixed243_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 7 := by decide +kernel
theorem a_fixed243_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a243.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.a243.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 9 := by decide +kernel
theorem ranks243_linked : ReferenceRankData.CoarseLowerShape.Batch0030.targetR243=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0030.targetA243=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 1 := by decide +kernel
theorem r_input243_linked : ReferenceRankData.CoarseLowerShape.Batch0030.r243.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds.gauge] := by decide +kernel
theorem a_input243_linked : ReferenceRankData.CoarseLowerShape.Batch0030.a243.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.a243.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.a243.bounds.gauge] := by decide +kernel
theorem geometry243_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.a := by decide +kernel
theorem weights486_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0060.cert486.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights487_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0060.cert487.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time243_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 10)=true := by decide +kernel
theorem r_reference243_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 0)=true := by decide +kernel
theorem a_reference243_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 1)=true := by decide +kernel
theorem rank_r_link243_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r243 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link243_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0030.a243.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a243 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints243 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell true ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r243 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile243_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link243_checked
    geometry243_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell false ReferenceProfileData.CoarseLowerShape.Batch0030.a243.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a243 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile243_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link243_checked
    geometry243_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks243_linked.1,←ranks243_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0030.r243.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a243.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0030.ordered243_checked hr ha ho
theorem frozen_frame243 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243 ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds ReferenceProfileData.CoarseLowerShape.Batch0030.a243.bounds
  · rw [←r_profile243_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile243_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry243_linked.2.2.2.2.1
  · exact geometry243_linked.2.2.2.2.2
  · exact r_reference243_checked
  · exact a_reference243_checked
  · exact r_fixed243_linked
  · exact a_fixed243_linked
  · exact time243_checked
  · exact ht
  · exact hw
theorem child_geometry243_checked : ReferenceWeightData.CoarseLowerShape.Batch0060.cert486.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0060.cert486.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0060.cert487.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0060.cert487.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights243 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0060.cert486∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch60_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0060.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0060.cert487∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch60_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0060.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0060.cert486.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0060.cert486.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0060.cert486.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry243_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights486_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0060.cert487.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0060.cert487.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry243_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry243_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights487_linked j (List.mem_finRange j))
theorem actual_frozen_frame243 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame243 (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.flow.timeParameter_mem child_geometry243_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights243 hz)
theorem r_profile244_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r244=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds := by rfl
theorem a_profile244_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a244=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a244.bounds := by rfl
theorem r_fixed244_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 7 := by decide +kernel
theorem a_fixed244_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a244.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.a244.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 9 := by decide +kernel
theorem ranks244_linked : ReferenceRankData.CoarseLowerShape.Batch0030.targetR244=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0030.targetA244=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 1 := by decide +kernel
theorem r_input244_linked : ReferenceRankData.CoarseLowerShape.Batch0030.r244.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds.gauge] := by decide +kernel
theorem a_input244_linked : ReferenceRankData.CoarseLowerShape.Batch0030.a244.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.a244.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.a244.bounds.gauge] := by decide +kernel
theorem geometry244_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.a := by decide +kernel
theorem weights488_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0061.cert488.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights489_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0061.cert489.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time244_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 10)=true := by decide +kernel
theorem r_reference244_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 0)=true := by decide +kernel
theorem a_reference244_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 1)=true := by decide +kernel
theorem rank_r_link244_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r244 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link244_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0030.a244.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a244 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints244 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell true ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r244 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile244_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link244_checked
    geometry244_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell false ReferenceProfileData.CoarseLowerShape.Batch0030.a244.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a244 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile244_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link244_checked
    geometry244_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks244_linked.1,←ranks244_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0030.r244.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a244.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0030.ordered244_checked hr ha ho
theorem frozen_frame244 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244 ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds ReferenceProfileData.CoarseLowerShape.Batch0030.a244.bounds
  · rw [←r_profile244_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile244_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry244_linked.2.2.2.2.1
  · exact geometry244_linked.2.2.2.2.2
  · exact r_reference244_checked
  · exact a_reference244_checked
  · exact r_fixed244_linked
  · exact a_fixed244_linked
  · exact time244_checked
  · exact ht
  · exact hw
theorem child_geometry244_checked : ReferenceWeightData.CoarseLowerShape.Batch0061.cert488.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0061.cert488.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0061.cert489.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0061.cert489.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights244 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0061.cert488∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch61_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0061.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0061.cert489∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch61_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0061.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0061.cert488.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0061.cert488.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0061.cert488.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry244_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights488_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0061.cert489.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0061.cert489.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry244_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry244_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights489_linked j (List.mem_finRange j))
theorem actual_frozen_frame244 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame244 (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.flow.timeParameter_mem child_geometry244_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights244 hz)
theorem r_profile245_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r245=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds := by rfl
theorem a_profile245_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a245=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a245.bounds := by rfl
theorem r_fixed245_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 7 := by decide +kernel
theorem a_fixed245_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a245.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.a245.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 9 := by decide +kernel
theorem ranks245_linked : ReferenceRankData.CoarseLowerShape.Batch0030.targetR245=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0030.targetA245=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 1 := by decide +kernel
theorem r_input245_linked : ReferenceRankData.CoarseLowerShape.Batch0030.r245.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds.gauge] := by decide +kernel
theorem a_input245_linked : ReferenceRankData.CoarseLowerShape.Batch0030.a245.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.a245.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.a245.bounds.gauge] := by decide +kernel
theorem geometry245_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.a := by decide +kernel
theorem weights490_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0061.cert490.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights491_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0061.cert491.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time245_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 10)=true := by decide +kernel
theorem r_reference245_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 0)=true := by decide +kernel
theorem a_reference245_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 1)=true := by decide +kernel
theorem rank_r_link245_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r245 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link245_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0030.a245.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a245 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints245 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell true ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r245 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile245_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link245_checked
    geometry245_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell false ReferenceProfileData.CoarseLowerShape.Batch0030.a245.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a245 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile245_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link245_checked
    geometry245_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks245_linked.1,←ranks245_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0030.r245.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a245.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0030.ordered245_checked hr ha ho
theorem frozen_frame245 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245 ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds ReferenceProfileData.CoarseLowerShape.Batch0030.a245.bounds
  · rw [←r_profile245_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile245_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry245_linked.2.2.2.2.1
  · exact geometry245_linked.2.2.2.2.2
  · exact r_reference245_checked
  · exact a_reference245_checked
  · exact r_fixed245_linked
  · exact a_fixed245_linked
  · exact time245_checked
  · exact ht
  · exact hw
theorem child_geometry245_checked : ReferenceWeightData.CoarseLowerShape.Batch0061.cert490.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0061.cert490.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0061.cert491.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0061.cert491.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights245 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0061.cert490∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch61_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0061.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0061.cert491∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch61_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0061.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0061.cert490.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0061.cert490.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0061.cert490.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry245_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights490_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0061.cert491.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0061.cert491.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry245_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry245_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights491_linked j (List.mem_finRange j))
theorem actual_frozen_frame245 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame245 (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.flow.timeParameter_mem child_geometry245_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights245 hz)
theorem r_profile246_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r246=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds := by rfl
theorem a_profile246_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a246=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a246.bounds := by rfl
theorem r_fixed246_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 7 := by decide +kernel
theorem a_fixed246_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a246.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.a246.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 9 := by decide +kernel
theorem ranks246_linked : ReferenceRankData.CoarseLowerShape.Batch0030.targetR246=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0030.targetA246=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 1 := by decide +kernel
theorem r_input246_linked : ReferenceRankData.CoarseLowerShape.Batch0030.r246.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds.gauge] := by decide +kernel
theorem a_input246_linked : ReferenceRankData.CoarseLowerShape.Batch0030.a246.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.a246.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.a246.bounds.gauge] := by decide +kernel
theorem geometry246_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.a := by decide +kernel
theorem weights492_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0061.cert492.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights493_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0061.cert493.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time246_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 10)=true := by decide +kernel
theorem r_reference246_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 0)=true := by decide +kernel
theorem a_reference246_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 1)=true := by decide +kernel
theorem rank_r_link246_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r246 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link246_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0030.a246.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a246 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints246 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell true ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r246 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile246_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link246_checked
    geometry246_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell false ReferenceProfileData.CoarseLowerShape.Batch0030.a246.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a246 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile246_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link246_checked
    geometry246_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks246_linked.1,←ranks246_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0030.r246.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a246.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0030.ordered246_checked hr ha ho
theorem frozen_frame246 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246 ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds ReferenceProfileData.CoarseLowerShape.Batch0030.a246.bounds
  · rw [←r_profile246_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile246_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry246_linked.2.2.2.2.1
  · exact geometry246_linked.2.2.2.2.2
  · exact r_reference246_checked
  · exact a_reference246_checked
  · exact r_fixed246_linked
  · exact a_fixed246_linked
  · exact time246_checked
  · exact ht
  · exact hw
theorem child_geometry246_checked : ReferenceWeightData.CoarseLowerShape.Batch0061.cert492.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0061.cert492.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0061.cert493.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0061.cert493.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights246 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0061.cert492∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch61_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0061.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0061.cert493∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch61_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0061.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0061.cert492.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0061.cert492.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0061.cert492.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry246_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights492_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0061.cert493.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0061.cert493.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry246_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry246_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights493_linked j (List.mem_finRange j))
theorem actual_frozen_frame246 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame246 (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.flow.timeParameter_mem child_geometry246_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights246 hz)
theorem r_profile247_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r247=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds := by rfl
theorem a_profile247_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a247=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a247.bounds := by rfl
theorem r_fixed247_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 7 := by decide +kernel
theorem a_fixed247_linked : ReferenceProfileData.CoarseLowerShape.Batch0030.a247.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0030.a247.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 9 := by decide +kernel
theorem ranks247_linked : ReferenceRankData.CoarseLowerShape.Batch0030.targetR247=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0030.targetA247=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 1 := by decide +kernel
theorem r_input247_linked : ReferenceRankData.CoarseLowerShape.Batch0030.r247.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds.gauge] := by decide +kernel
theorem a_input247_linked : ReferenceRankData.CoarseLowerShape.Batch0030.a247.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0030.a247.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0030.a247.bounds.gauge] := by decide +kernel
theorem geometry247_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.a := by decide +kernel
theorem weights494_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0061.cert494.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights495_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0061.cert495.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time247_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 10)=true := by decide +kernel
theorem r_reference247_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 0)=true := by decide +kernel
theorem a_reference247_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 1)=true := by decide +kernel
theorem rank_r_link247_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r247 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link247_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0030.a247.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a247 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints247 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell true ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds ReferenceRankData.CoarseLowerShape.Batch0030.r247 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile247_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link247_checked
    geometry247_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell false ReferenceProfileData.CoarseLowerShape.Batch0030.a247.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a247 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile247_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0030.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0030.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link247_checked
    geometry247_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks247_linked.1,←ranks247_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0030.r247.bounds ReferenceRankData.CoarseLowerShape.Batch0030.a247.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0030.ordered247_checked hr ha ho
theorem frozen_frame247 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247 ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds ReferenceProfileData.CoarseLowerShape.Batch0030.a247.bounds
  · rw [←r_profile247_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile247_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry247_linked.2.2.2.2.1
  · exact geometry247_linked.2.2.2.2.2
  · exact r_reference247_checked
  · exact a_reference247_checked
  · exact r_fixed247_linked
  · exact a_fixed247_linked
  · exact time247_checked
  · exact ht
  · exact hw
theorem child_geometry247_checked : ReferenceWeightData.CoarseLowerShape.Batch0061.cert494.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0061.cert494.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0061.cert495.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0061.cert495.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights247 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0061.cert494∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch61_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0061.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0061.cert495∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch61_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0061.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0061.cert494.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0061.cert494.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0061.cert494.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry247_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights494_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0061.cert495.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0061.cert495.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry247_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry247_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights495_linked j (List.mem_finRange j))
theorem actual_frozen_frame247 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame247 (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.flow.timeParameter_mem child_geometry247_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights247 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell240),(ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell241),(ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell242),(ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell243),(ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell244),(ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell245),(ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell246),(ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0030.cell247)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0030.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0030.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame240 hz
  · exact fun z hz=>actual_frozen_frame241 hz
  · exact fun z hz=>actual_frozen_frame242 hz
  · exact fun z hz=>actual_frozen_frame243 hz
  · exact fun z hz=>actual_frozen_frame244 hz
  · exact fun z hz=>actual_frozen_frame245 hz
  · exact fun z hz=>actual_frozen_frame246 hz
  · exact fun z hz=>actual_frozen_frame247 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints240 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints241 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints242 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints243 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints244 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints245 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints246 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints247 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry240_linked.1,geometry240_linked.2.1,geometry240_linked.2.2.1,geometry240_linked.2.2.2.1⟩
  · exact ⟨geometry241_linked.1,geometry241_linked.2.1,geometry241_linked.2.2.1,geometry241_linked.2.2.2.1⟩
  · exact ⟨geometry242_linked.1,geometry242_linked.2.1,geometry242_linked.2.2.1,geometry242_linked.2.2.2.1⟩
  · exact ⟨geometry243_linked.1,geometry243_linked.2.1,geometry243_linked.2.2.1,geometry243_linked.2.2.2.1⟩
  · exact ⟨geometry244_linked.1,geometry244_linked.2.1,geometry244_linked.2.2.1,geometry244_linked.2.2.2.1⟩
  · exact ⟨geometry245_linked.1,geometry245_linked.2.1,geometry245_linked.2.2.1,geometry245_linked.2.2.2.1⟩
  · exact ⟨geometry246_linked.1,geometry246_linked.2.1,geometry246_linked.2.2.1,geometry246_linked.2.2.2.1⟩
  · exact ⟨geometry247_linked.1,geometry247_linked.2.1,geometry247_linked.2.2.1,geometry247_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.a240.bounds,?_,geometry240_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a240.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile240_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds,?_,geometry240_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert240.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r240.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile240_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.a241.bounds,?_,geometry241_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a241.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile241_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds,?_,geometry241_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert241.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r241.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile241_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.a242.bounds,?_,geometry242_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a242.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile242_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds,?_,geometry242_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert242.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r242.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile242_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.a243.bounds,?_,geometry243_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a243.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile243_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds,?_,geometry243_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert243.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r243.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile243_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.a244.bounds,?_,geometry244_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a244.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile244_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds,?_,geometry244_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert244.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r244.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile244_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.a245.bounds,?_,geometry245_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a245.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile245_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds,?_,geometry245_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert245.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r245.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile245_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.a246.bounds,?_,geometry246_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a246.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile246_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds,?_,geometry246_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert246.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r246.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile246_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.a247.bounds,?_,geometry247_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0030.a247.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile247_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds,?_,geometry247_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0030.cert247.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0030.r247.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile247_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0030.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0030.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0030

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0031
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch62_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0062.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0062.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch63_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0063.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0063.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile248_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r248=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds := by rfl
theorem a_profile248_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a248=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a248.bounds := by rfl
theorem r_fixed248_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 7 := by decide +kernel
theorem a_fixed248_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a248.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.a248.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 9 := by decide +kernel
theorem ranks248_linked : ReferenceRankData.CoarseLowerShape.Batch0031.targetR248=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0031.targetA248=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 1 := by decide +kernel
theorem r_input248_linked : ReferenceRankData.CoarseLowerShape.Batch0031.r248.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds.gauge] := by decide +kernel
theorem a_input248_linked : ReferenceRankData.CoarseLowerShape.Batch0031.a248.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.a248.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.a248.bounds.gauge] := by decide +kernel
theorem geometry248_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.a := by decide +kernel
theorem weights496_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0062.cert496.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights497_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0062.cert497.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time248_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 10)=true := by decide +kernel
theorem r_reference248_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 0)=true := by decide +kernel
theorem a_reference248_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 1)=true := by decide +kernel
theorem rank_r_link248_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r248 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link248_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0031.a248.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a248 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints248 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell true ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r248 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile248_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link248_checked
    geometry248_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell false ReferenceProfileData.CoarseLowerShape.Batch0031.a248.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a248 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile248_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link248_checked
    geometry248_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks248_linked.1,←ranks248_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0031.r248.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a248.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0031.ordered248_checked hr ha ho
theorem frozen_frame248 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248 ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds ReferenceProfileData.CoarseLowerShape.Batch0031.a248.bounds
  · rw [←r_profile248_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile248_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry248_linked.2.2.2.2.1
  · exact geometry248_linked.2.2.2.2.2
  · exact r_reference248_checked
  · exact a_reference248_checked
  · exact r_fixed248_linked
  · exact a_fixed248_linked
  · exact time248_checked
  · exact ht
  · exact hw
theorem child_geometry248_checked : ReferenceWeightData.CoarseLowerShape.Batch0062.cert496.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0062.cert496.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0062.cert497.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0062.cert497.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights248 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0062.cert496∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch62_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0062.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0062.cert497∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch62_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0062.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0062.cert496.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0062.cert496.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0062.cert496.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry248_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights496_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0062.cert497.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0062.cert497.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry248_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry248_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights497_linked j (List.mem_finRange j))
theorem actual_frozen_frame248 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame248 (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.flow.timeParameter_mem child_geometry248_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights248 hz)
theorem r_profile249_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r249=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds := by rfl
theorem a_profile249_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a249=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a249.bounds := by rfl
theorem r_fixed249_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 7 := by decide +kernel
theorem a_fixed249_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a249.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.a249.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 9 := by decide +kernel
theorem ranks249_linked : ReferenceRankData.CoarseLowerShape.Batch0031.targetR249=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0031.targetA249=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 1 := by decide +kernel
theorem r_input249_linked : ReferenceRankData.CoarseLowerShape.Batch0031.r249.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds.gauge] := by decide +kernel
theorem a_input249_linked : ReferenceRankData.CoarseLowerShape.Batch0031.a249.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.a249.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.a249.bounds.gauge] := by decide +kernel
theorem geometry249_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.a := by decide +kernel
theorem weights498_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0062.cert498.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights499_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0062.cert499.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time249_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 10)=true := by decide +kernel
theorem r_reference249_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 0)=true := by decide +kernel
theorem a_reference249_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 1)=true := by decide +kernel
theorem rank_r_link249_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r249 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link249_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0031.a249.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a249 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints249 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell true ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r249 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile249_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link249_checked
    geometry249_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell false ReferenceProfileData.CoarseLowerShape.Batch0031.a249.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a249 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile249_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link249_checked
    geometry249_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks249_linked.1,←ranks249_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0031.r249.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a249.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0031.ordered249_checked hr ha ho
theorem frozen_frame249 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249 ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds ReferenceProfileData.CoarseLowerShape.Batch0031.a249.bounds
  · rw [←r_profile249_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile249_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry249_linked.2.2.2.2.1
  · exact geometry249_linked.2.2.2.2.2
  · exact r_reference249_checked
  · exact a_reference249_checked
  · exact r_fixed249_linked
  · exact a_fixed249_linked
  · exact time249_checked
  · exact ht
  · exact hw
theorem child_geometry249_checked : ReferenceWeightData.CoarseLowerShape.Batch0062.cert498.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0062.cert498.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0062.cert499.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0062.cert499.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights249 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0062.cert498∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch62_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0062.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0062.cert499∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch62_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0062.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0062.cert498.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0062.cert498.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0062.cert498.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry249_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights498_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0062.cert499.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0062.cert499.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry249_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry249_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights499_linked j (List.mem_finRange j))
theorem actual_frozen_frame249 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame249 (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.flow.timeParameter_mem child_geometry249_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights249 hz)
theorem r_profile250_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r250=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds := by rfl
theorem a_profile250_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a250=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a250.bounds := by rfl
theorem r_fixed250_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 7 := by decide +kernel
theorem a_fixed250_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a250.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.a250.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 9 := by decide +kernel
theorem ranks250_linked : ReferenceRankData.CoarseLowerShape.Batch0031.targetR250=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0031.targetA250=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 1 := by decide +kernel
theorem r_input250_linked : ReferenceRankData.CoarseLowerShape.Batch0031.r250.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds.gauge] := by decide +kernel
theorem a_input250_linked : ReferenceRankData.CoarseLowerShape.Batch0031.a250.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.a250.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.a250.bounds.gauge] := by decide +kernel
theorem geometry250_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.a := by decide +kernel
theorem weights500_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0062.cert500.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights501_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0062.cert501.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time250_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 10)=true := by decide +kernel
theorem r_reference250_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 0)=true := by decide +kernel
theorem a_reference250_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 1)=true := by decide +kernel
theorem rank_r_link250_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r250 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link250_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0031.a250.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a250 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints250 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell true ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r250 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile250_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link250_checked
    geometry250_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell false ReferenceProfileData.CoarseLowerShape.Batch0031.a250.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a250 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile250_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link250_checked
    geometry250_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks250_linked.1,←ranks250_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0031.r250.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a250.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0031.ordered250_checked hr ha ho
theorem frozen_frame250 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250 ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds ReferenceProfileData.CoarseLowerShape.Batch0031.a250.bounds
  · rw [←r_profile250_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile250_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry250_linked.2.2.2.2.1
  · exact geometry250_linked.2.2.2.2.2
  · exact r_reference250_checked
  · exact a_reference250_checked
  · exact r_fixed250_linked
  · exact a_fixed250_linked
  · exact time250_checked
  · exact ht
  · exact hw
theorem child_geometry250_checked : ReferenceWeightData.CoarseLowerShape.Batch0062.cert500.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0062.cert500.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0062.cert501.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0062.cert501.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights250 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0062.cert500∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch62_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0062.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0062.cert501∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch62_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0062.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0062.cert500.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0062.cert500.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0062.cert500.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry250_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights500_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0062.cert501.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0062.cert501.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry250_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry250_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights501_linked j (List.mem_finRange j))
theorem actual_frozen_frame250 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame250 (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.flow.timeParameter_mem child_geometry250_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights250 hz)
theorem r_profile251_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r251=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds := by rfl
theorem a_profile251_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a251=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a251.bounds := by rfl
theorem r_fixed251_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 7 := by decide +kernel
theorem a_fixed251_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a251.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.a251.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 9 := by decide +kernel
theorem ranks251_linked : ReferenceRankData.CoarseLowerShape.Batch0031.targetR251=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0031.targetA251=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 1 := by decide +kernel
theorem r_input251_linked : ReferenceRankData.CoarseLowerShape.Batch0031.r251.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds.gauge] := by decide +kernel
theorem a_input251_linked : ReferenceRankData.CoarseLowerShape.Batch0031.a251.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.a251.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.a251.bounds.gauge] := by decide +kernel
theorem geometry251_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.a := by decide +kernel
theorem weights502_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0062.cert502.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights503_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0062.cert503.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time251_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 10)=true := by decide +kernel
theorem r_reference251_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 0)=true := by decide +kernel
theorem a_reference251_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 1)=true := by decide +kernel
theorem rank_r_link251_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r251 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link251_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0031.a251.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a251 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints251 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell true ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r251 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile251_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link251_checked
    geometry251_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell false ReferenceProfileData.CoarseLowerShape.Batch0031.a251.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a251 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile251_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link251_checked
    geometry251_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks251_linked.1,←ranks251_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0031.r251.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a251.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0031.ordered251_checked hr ha ho
theorem frozen_frame251 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251 ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds ReferenceProfileData.CoarseLowerShape.Batch0031.a251.bounds
  · rw [←r_profile251_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile251_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry251_linked.2.2.2.2.1
  · exact geometry251_linked.2.2.2.2.2
  · exact r_reference251_checked
  · exact a_reference251_checked
  · exact r_fixed251_linked
  · exact a_fixed251_linked
  · exact time251_checked
  · exact ht
  · exact hw
theorem child_geometry251_checked : ReferenceWeightData.CoarseLowerShape.Batch0062.cert502.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0062.cert502.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0062.cert503.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0062.cert503.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights251 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0062.cert502∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch62_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0062.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0062.cert503∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch62_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0062.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0062.cert502.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0062.cert502.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0062.cert502.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry251_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights502_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0062.cert503.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0062.cert503.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry251_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry251_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights503_linked j (List.mem_finRange j))
theorem actual_frozen_frame251 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame251 (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.flow.timeParameter_mem child_geometry251_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights251 hz)
theorem r_profile252_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r252=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds := by rfl
theorem a_profile252_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a252=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a252.bounds := by rfl
theorem r_fixed252_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 7 := by decide +kernel
theorem a_fixed252_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a252.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.a252.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 9 := by decide +kernel
theorem ranks252_linked : ReferenceRankData.CoarseLowerShape.Batch0031.targetR252=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0031.targetA252=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 1 := by decide +kernel
theorem r_input252_linked : ReferenceRankData.CoarseLowerShape.Batch0031.r252.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds.gauge] := by decide +kernel
theorem a_input252_linked : ReferenceRankData.CoarseLowerShape.Batch0031.a252.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.a252.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.a252.bounds.gauge] := by decide +kernel
theorem geometry252_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.a := by decide +kernel
theorem weights504_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0063.cert504.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights505_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0063.cert505.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time252_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 10)=true := by decide +kernel
theorem r_reference252_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 0)=true := by decide +kernel
theorem a_reference252_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 1)=true := by decide +kernel
theorem rank_r_link252_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r252 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link252_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0031.a252.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a252 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints252 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell true ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r252 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile252_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link252_checked
    geometry252_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell false ReferenceProfileData.CoarseLowerShape.Batch0031.a252.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a252 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile252_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link252_checked
    geometry252_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks252_linked.1,←ranks252_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0031.r252.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a252.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0031.ordered252_checked hr ha ho
theorem frozen_frame252 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252 ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds ReferenceProfileData.CoarseLowerShape.Batch0031.a252.bounds
  · rw [←r_profile252_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile252_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry252_linked.2.2.2.2.1
  · exact geometry252_linked.2.2.2.2.2
  · exact r_reference252_checked
  · exact a_reference252_checked
  · exact r_fixed252_linked
  · exact a_fixed252_linked
  · exact time252_checked
  · exact ht
  · exact hw
theorem child_geometry252_checked : ReferenceWeightData.CoarseLowerShape.Batch0063.cert504.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0063.cert504.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0063.cert505.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0063.cert505.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights252 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0063.cert504∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch63_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0063.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0063.cert505∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch63_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0063.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0063.cert504.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0063.cert504.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0063.cert504.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry252_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights504_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0063.cert505.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0063.cert505.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry252_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry252_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights505_linked j (List.mem_finRange j))
theorem actual_frozen_frame252 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame252 (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.flow.timeParameter_mem child_geometry252_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights252 hz)
theorem r_profile253_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r253=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds := by rfl
theorem a_profile253_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a253=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a253.bounds := by rfl
theorem r_fixed253_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 7 := by decide +kernel
theorem a_fixed253_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a253.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.a253.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 9 := by decide +kernel
theorem ranks253_linked : ReferenceRankData.CoarseLowerShape.Batch0031.targetR253=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0031.targetA253=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 1 := by decide +kernel
theorem r_input253_linked : ReferenceRankData.CoarseLowerShape.Batch0031.r253.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds.gauge] := by decide +kernel
theorem a_input253_linked : ReferenceRankData.CoarseLowerShape.Batch0031.a253.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.a253.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.a253.bounds.gauge] := by decide +kernel
theorem geometry253_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.a := by decide +kernel
theorem weights506_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0063.cert506.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights507_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0063.cert507.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time253_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 10)=true := by decide +kernel
theorem r_reference253_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 0)=true := by decide +kernel
theorem a_reference253_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 1)=true := by decide +kernel
theorem rank_r_link253_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r253 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link253_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0031.a253.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a253 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints253 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell true ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r253 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile253_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link253_checked
    geometry253_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell false ReferenceProfileData.CoarseLowerShape.Batch0031.a253.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a253 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile253_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link253_checked
    geometry253_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks253_linked.1,←ranks253_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0031.r253.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a253.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0031.ordered253_checked hr ha ho
theorem frozen_frame253 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253 ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds ReferenceProfileData.CoarseLowerShape.Batch0031.a253.bounds
  · rw [←r_profile253_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile253_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry253_linked.2.2.2.2.1
  · exact geometry253_linked.2.2.2.2.2
  · exact r_reference253_checked
  · exact a_reference253_checked
  · exact r_fixed253_linked
  · exact a_fixed253_linked
  · exact time253_checked
  · exact ht
  · exact hw
theorem child_geometry253_checked : ReferenceWeightData.CoarseLowerShape.Batch0063.cert506.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0063.cert506.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0063.cert507.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0063.cert507.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights253 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0063.cert506∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch63_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0063.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0063.cert507∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch63_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0063.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0063.cert506.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0063.cert506.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0063.cert506.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry253_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights506_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0063.cert507.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0063.cert507.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry253_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry253_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights507_linked j (List.mem_finRange j))
theorem actual_frozen_frame253 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame253 (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.flow.timeParameter_mem child_geometry253_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights253 hz)
theorem r_profile254_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r254=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds := by rfl
theorem a_profile254_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a254=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a254.bounds := by rfl
theorem r_fixed254_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 7 := by decide +kernel
theorem a_fixed254_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a254.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.a254.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 9 := by decide +kernel
theorem ranks254_linked : ReferenceRankData.CoarseLowerShape.Batch0031.targetR254=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0031.targetA254=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 1 := by decide +kernel
theorem r_input254_linked : ReferenceRankData.CoarseLowerShape.Batch0031.r254.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds.gauge] := by decide +kernel
theorem a_input254_linked : ReferenceRankData.CoarseLowerShape.Batch0031.a254.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.a254.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.a254.bounds.gauge] := by decide +kernel
theorem geometry254_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.a := by decide +kernel
theorem weights508_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0063.cert508.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights509_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0063.cert509.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time254_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 10)=true := by decide +kernel
theorem r_reference254_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 0)=true := by decide +kernel
theorem a_reference254_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 1)=true := by decide +kernel
theorem rank_r_link254_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r254 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link254_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0031.a254.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a254 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints254 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell true ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r254 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile254_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link254_checked
    geometry254_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell false ReferenceProfileData.CoarseLowerShape.Batch0031.a254.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a254 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile254_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link254_checked
    geometry254_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks254_linked.1,←ranks254_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0031.r254.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a254.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0031.ordered254_checked hr ha ho
theorem frozen_frame254 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254 ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds ReferenceProfileData.CoarseLowerShape.Batch0031.a254.bounds
  · rw [←r_profile254_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile254_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry254_linked.2.2.2.2.1
  · exact geometry254_linked.2.2.2.2.2
  · exact r_reference254_checked
  · exact a_reference254_checked
  · exact r_fixed254_linked
  · exact a_fixed254_linked
  · exact time254_checked
  · exact ht
  · exact hw
theorem child_geometry254_checked : ReferenceWeightData.CoarseLowerShape.Batch0063.cert508.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0063.cert508.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0063.cert509.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0063.cert509.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights254 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0063.cert508∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch63_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0063.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0063.cert509∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch63_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0063.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0063.cert508.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0063.cert508.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0063.cert508.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry254_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights508_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0063.cert509.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0063.cert509.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry254_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry254_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights509_linked j (List.mem_finRange j))
theorem actual_frozen_frame254 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame254 (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.flow.timeParameter_mem child_geometry254_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights254 hz)
theorem r_profile255_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r255=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds := by rfl
theorem a_profile255_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a255=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a255.bounds := by rfl
theorem r_fixed255_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 7 := by decide +kernel
theorem a_fixed255_linked : ReferenceProfileData.CoarseLowerShape.Batch0031.a255.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0031.a255.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 9 := by decide +kernel
theorem ranks255_linked : ReferenceRankData.CoarseLowerShape.Batch0031.targetR255=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0031.targetA255=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 1 := by decide +kernel
theorem r_input255_linked : ReferenceRankData.CoarseLowerShape.Batch0031.r255.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds.gauge] := by decide +kernel
theorem a_input255_linked : ReferenceRankData.CoarseLowerShape.Batch0031.a255.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0031.a255.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0031.a255.bounds.gauge] := by decide +kernel
theorem geometry255_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.a := by decide +kernel
theorem weights510_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0063.cert510.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights511_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0063.cert511.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time255_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 10)=true := by decide +kernel
theorem r_reference255_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 0)=true := by decide +kernel
theorem a_reference255_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 1)=true := by decide +kernel
theorem rank_r_link255_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r255 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link255_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0031.a255.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a255 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints255 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell true ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds ReferenceRankData.CoarseLowerShape.Batch0031.r255 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile255_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link255_checked
    geometry255_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell false ReferenceProfileData.CoarseLowerShape.Batch0031.a255.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a255 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile255_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0031.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0031.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link255_checked
    geometry255_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks255_linked.1,←ranks255_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0031.r255.bounds ReferenceRankData.CoarseLowerShape.Batch0031.a255.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0031.ordered255_checked hr ha ho
theorem frozen_frame255 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255 ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds ReferenceProfileData.CoarseLowerShape.Batch0031.a255.bounds
  · rw [←r_profile255_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile255_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry255_linked.2.2.2.2.1
  · exact geometry255_linked.2.2.2.2.2
  · exact r_reference255_checked
  · exact a_reference255_checked
  · exact r_fixed255_linked
  · exact a_fixed255_linked
  · exact time255_checked
  · exact ht
  · exact hw
theorem child_geometry255_checked : ReferenceWeightData.CoarseLowerShape.Batch0063.cert510.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0063.cert510.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0063.cert511.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0063.cert511.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights255 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0063.cert510∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch63_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0063.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0063.cert511∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch63_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0063.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0063.cert510.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0063.cert510.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0063.cert510.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry255_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights510_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0063.cert511.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0063.cert511.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry255_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry255_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights511_linked j (List.mem_finRange j))
theorem actual_frozen_frame255 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame255 (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.flow.timeParameter_mem child_geometry255_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights255 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell248),(ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell249),(ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell250),(ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell251),(ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell252),(ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell253),(ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell254),(ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0031.cell255)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0031.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0031.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame248 hz
  · exact fun z hz=>actual_frozen_frame249 hz
  · exact fun z hz=>actual_frozen_frame250 hz
  · exact fun z hz=>actual_frozen_frame251 hz
  · exact fun z hz=>actual_frozen_frame252 hz
  · exact fun z hz=>actual_frozen_frame253 hz
  · exact fun z hz=>actual_frozen_frame254 hz
  · exact fun z hz=>actual_frozen_frame255 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints248 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints249 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints250 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints251 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints252 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints253 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints254 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints255 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry248_linked.1,geometry248_linked.2.1,geometry248_linked.2.2.1,geometry248_linked.2.2.2.1⟩
  · exact ⟨geometry249_linked.1,geometry249_linked.2.1,geometry249_linked.2.2.1,geometry249_linked.2.2.2.1⟩
  · exact ⟨geometry250_linked.1,geometry250_linked.2.1,geometry250_linked.2.2.1,geometry250_linked.2.2.2.1⟩
  · exact ⟨geometry251_linked.1,geometry251_linked.2.1,geometry251_linked.2.2.1,geometry251_linked.2.2.2.1⟩
  · exact ⟨geometry252_linked.1,geometry252_linked.2.1,geometry252_linked.2.2.1,geometry252_linked.2.2.2.1⟩
  · exact ⟨geometry253_linked.1,geometry253_linked.2.1,geometry253_linked.2.2.1,geometry253_linked.2.2.2.1⟩
  · exact ⟨geometry254_linked.1,geometry254_linked.2.1,geometry254_linked.2.2.1,geometry254_linked.2.2.2.1⟩
  · exact ⟨geometry255_linked.1,geometry255_linked.2.1,geometry255_linked.2.2.1,geometry255_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.a248.bounds,?_,geometry248_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a248.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile248_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds,?_,geometry248_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert248.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r248.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile248_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.a249.bounds,?_,geometry249_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a249.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile249_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds,?_,geometry249_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert249.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r249.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile249_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.a250.bounds,?_,geometry250_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a250.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile250_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds,?_,geometry250_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert250.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r250.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile250_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.a251.bounds,?_,geometry251_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a251.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile251_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds,?_,geometry251_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert251.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r251.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile251_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.a252.bounds,?_,geometry252_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a252.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile252_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds,?_,geometry252_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert252.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r252.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile252_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.a253.bounds,?_,geometry253_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a253.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile253_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds,?_,geometry253_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert253.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r253.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile253_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.a254.bounds,?_,geometry254_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a254.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile254_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds,?_,geometry254_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert254.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r254.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile254_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.a255.bounds,?_,geometry255_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0031.a255.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile255_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds,?_,geometry255_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0031.cert255.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0031.r255.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile255_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0031.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0031.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0031
