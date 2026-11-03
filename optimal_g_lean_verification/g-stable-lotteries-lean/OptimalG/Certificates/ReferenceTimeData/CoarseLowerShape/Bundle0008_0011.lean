import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0005_0008
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0005_0008
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0017_0020
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0008_0011
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0007_0010
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0007
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0009_0012
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0009_0012
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0021_0024
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0011_0014

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0008
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch16_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0016.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0016.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch17_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0017.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0017.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile64_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r64=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds := by rfl
theorem a_profile64_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a64=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a64.bounds := by rfl
theorem r_fixed64_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 7 := by decide +kernel
theorem a_fixed64_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a64.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.a64.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 9 := by decide +kernel
theorem ranks64_linked : ReferenceRankData.CoarseLowerShape.Batch0008.targetR64=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0008.targetA64=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 1 := by decide +kernel
theorem r_input64_linked : ReferenceRankData.CoarseLowerShape.Batch0008.r64.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds.gauge] := by decide +kernel
theorem a_input64_linked : ReferenceRankData.CoarseLowerShape.Batch0008.a64.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.a64.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.a64.bounds.gauge] := by decide +kernel
theorem geometry64_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.a := by decide +kernel
theorem weights128_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0016.cert128.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights129_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0016.cert129.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time64_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 10)=true := by decide +kernel
theorem r_reference64_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 0)=true := by decide +kernel
theorem a_reference64_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 1)=true := by decide +kernel
theorem rank_r_link64_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r64 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link64_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0008.a64.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a64 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints64 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell true ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r64 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile64_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link64_checked
    geometry64_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell false ReferenceProfileData.CoarseLowerShape.Batch0008.a64.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a64 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile64_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link64_checked
    geometry64_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks64_linked.1,←ranks64_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0008.r64.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a64.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0008.ordered64_checked hr ha ho
theorem frozen_frame64 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64 ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds ReferenceProfileData.CoarseLowerShape.Batch0008.a64.bounds
  · rw [←r_profile64_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile64_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry64_linked.2.2.2.2.1
  · exact geometry64_linked.2.2.2.2.2
  · exact r_reference64_checked
  · exact a_reference64_checked
  · exact r_fixed64_linked
  · exact a_fixed64_linked
  · exact time64_checked
  · exact ht
  · exact hw
theorem child_geometry64_checked : ReferenceWeightData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights64 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0016.cert128∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch16_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0016.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0016.cert129∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch16_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0016.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0016.cert128.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry64_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights128_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0016.cert129.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry64_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry64_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights129_linked j (List.mem_finRange j))
theorem actual_frozen_frame64 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame64 (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.flow.timeParameter_mem child_geometry64_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights64 hz)
theorem r_profile65_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r65=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds := by rfl
theorem a_profile65_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a65=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a65.bounds := by rfl
theorem r_fixed65_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 7 := by decide +kernel
theorem a_fixed65_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a65.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.a65.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 9 := by decide +kernel
theorem ranks65_linked : ReferenceRankData.CoarseLowerShape.Batch0008.targetR65=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0008.targetA65=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 1 := by decide +kernel
theorem r_input65_linked : ReferenceRankData.CoarseLowerShape.Batch0008.r65.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds.gauge] := by decide +kernel
theorem a_input65_linked : ReferenceRankData.CoarseLowerShape.Batch0008.a65.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.a65.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.a65.bounds.gauge] := by decide +kernel
theorem geometry65_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.a := by decide +kernel
theorem weights130_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0016.cert130.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights131_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0016.cert131.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time65_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 10)=true := by decide +kernel
theorem r_reference65_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 0)=true := by decide +kernel
theorem a_reference65_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 1)=true := by decide +kernel
theorem rank_r_link65_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r65 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link65_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0008.a65.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a65 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints65 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell true ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r65 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile65_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link65_checked
    geometry65_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell false ReferenceProfileData.CoarseLowerShape.Batch0008.a65.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a65 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile65_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link65_checked
    geometry65_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks65_linked.1,←ranks65_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0008.r65.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a65.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0008.ordered65_checked hr ha ho
theorem frozen_frame65 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65 ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds ReferenceProfileData.CoarseLowerShape.Batch0008.a65.bounds
  · rw [←r_profile65_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile65_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry65_linked.2.2.2.2.1
  · exact geometry65_linked.2.2.2.2.2
  · exact r_reference65_checked
  · exact a_reference65_checked
  · exact r_fixed65_linked
  · exact a_fixed65_linked
  · exact time65_checked
  · exact ht
  · exact hw
theorem child_geometry65_checked : ReferenceWeightData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights65 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0016.cert130∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch16_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0016.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0016.cert131∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch16_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0016.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0016.cert130.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry65_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights130_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0016.cert131.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry65_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry65_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights131_linked j (List.mem_finRange j))
theorem actual_frozen_frame65 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame65 (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.flow.timeParameter_mem child_geometry65_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights65 hz)
theorem r_profile66_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r66=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds := by rfl
theorem a_profile66_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a66=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a66.bounds := by rfl
theorem r_fixed66_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 7 := by decide +kernel
theorem a_fixed66_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a66.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.a66.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 9 := by decide +kernel
theorem ranks66_linked : ReferenceRankData.CoarseLowerShape.Batch0008.targetR66=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0008.targetA66=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 1 := by decide +kernel
theorem r_input66_linked : ReferenceRankData.CoarseLowerShape.Batch0008.r66.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds.gauge] := by decide +kernel
theorem a_input66_linked : ReferenceRankData.CoarseLowerShape.Batch0008.a66.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.a66.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.a66.bounds.gauge] := by decide +kernel
theorem geometry66_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.a := by decide +kernel
theorem weights132_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0016.cert132.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights133_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0016.cert133.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time66_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 10)=true := by decide +kernel
theorem r_reference66_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 0)=true := by decide +kernel
theorem a_reference66_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 1)=true := by decide +kernel
theorem rank_r_link66_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r66 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link66_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0008.a66.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a66 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints66 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell true ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r66 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile66_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link66_checked
    geometry66_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell false ReferenceProfileData.CoarseLowerShape.Batch0008.a66.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a66 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile66_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link66_checked
    geometry66_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks66_linked.1,←ranks66_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0008.r66.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a66.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0008.ordered66_checked hr ha ho
theorem frozen_frame66 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66 ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds ReferenceProfileData.CoarseLowerShape.Batch0008.a66.bounds
  · rw [←r_profile66_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile66_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry66_linked.2.2.2.2.1
  · exact geometry66_linked.2.2.2.2.2
  · exact r_reference66_checked
  · exact a_reference66_checked
  · exact r_fixed66_linked
  · exact a_fixed66_linked
  · exact time66_checked
  · exact ht
  · exact hw
theorem child_geometry66_checked : ReferenceWeightData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights66 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0016.cert132∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch16_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0016.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0016.cert133∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch16_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0016.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0016.cert132.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry66_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights132_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0016.cert133.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry66_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry66_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights133_linked j (List.mem_finRange j))
theorem actual_frozen_frame66 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame66 (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.flow.timeParameter_mem child_geometry66_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights66 hz)
theorem r_profile67_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r67=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds := by rfl
theorem a_profile67_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a67=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a67.bounds := by rfl
theorem r_fixed67_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 7 := by decide +kernel
theorem a_fixed67_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a67.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.a67.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 9 := by decide +kernel
theorem ranks67_linked : ReferenceRankData.CoarseLowerShape.Batch0008.targetR67=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0008.targetA67=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 1 := by decide +kernel
theorem r_input67_linked : ReferenceRankData.CoarseLowerShape.Batch0008.r67.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds.gauge] := by decide +kernel
theorem a_input67_linked : ReferenceRankData.CoarseLowerShape.Batch0008.a67.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.a67.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.a67.bounds.gauge] := by decide +kernel
theorem geometry67_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.a := by decide +kernel
theorem weights134_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0016.cert134.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights135_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0016.cert135.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time67_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 10)=true := by decide +kernel
theorem r_reference67_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 0)=true := by decide +kernel
theorem a_reference67_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 1)=true := by decide +kernel
theorem rank_r_link67_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r67 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link67_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0008.a67.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a67 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints67 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell true ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r67 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile67_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link67_checked
    geometry67_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell false ReferenceProfileData.CoarseLowerShape.Batch0008.a67.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a67 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile67_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link67_checked
    geometry67_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks67_linked.1,←ranks67_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0008.r67.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a67.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0008.ordered67_checked hr ha ho
theorem frozen_frame67 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67 ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds ReferenceProfileData.CoarseLowerShape.Batch0008.a67.bounds
  · rw [←r_profile67_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile67_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry67_linked.2.2.2.2.1
  · exact geometry67_linked.2.2.2.2.2
  · exact r_reference67_checked
  · exact a_reference67_checked
  · exact r_fixed67_linked
  · exact a_fixed67_linked
  · exact time67_checked
  · exact ht
  · exact hw
theorem child_geometry67_checked : ReferenceWeightData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights67 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0016.cert134∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch16_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0016.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0016.cert135∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch16_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0016.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0016.cert134.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry67_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights134_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0016.cert135.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry67_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry67_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights135_linked j (List.mem_finRange j))
theorem actual_frozen_frame67 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame67 (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.flow.timeParameter_mem child_geometry67_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights67 hz)
theorem r_profile68_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r68=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds := by rfl
theorem a_profile68_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a68=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a68.bounds := by rfl
theorem r_fixed68_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 7 := by decide +kernel
theorem a_fixed68_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a68.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.a68.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 9 := by decide +kernel
theorem ranks68_linked : ReferenceRankData.CoarseLowerShape.Batch0008.targetR68=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0008.targetA68=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 1 := by decide +kernel
theorem r_input68_linked : ReferenceRankData.CoarseLowerShape.Batch0008.r68.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds.gauge] := by decide +kernel
theorem a_input68_linked : ReferenceRankData.CoarseLowerShape.Batch0008.a68.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.a68.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.a68.bounds.gauge] := by decide +kernel
theorem geometry68_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.a := by decide +kernel
theorem weights136_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0017.cert136.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights137_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0017.cert137.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time68_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 10)=true := by decide +kernel
theorem r_reference68_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 0)=true := by decide +kernel
theorem a_reference68_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 1)=true := by decide +kernel
theorem rank_r_link68_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r68 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link68_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0008.a68.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a68 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints68 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell true ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r68 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile68_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link68_checked
    geometry68_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell false ReferenceProfileData.CoarseLowerShape.Batch0008.a68.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a68 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile68_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link68_checked
    geometry68_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks68_linked.1,←ranks68_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0008.r68.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a68.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0008.ordered68_checked hr ha ho
theorem frozen_frame68 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68 ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds ReferenceProfileData.CoarseLowerShape.Batch0008.a68.bounds
  · rw [←r_profile68_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile68_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry68_linked.2.2.2.2.1
  · exact geometry68_linked.2.2.2.2.2
  · exact r_reference68_checked
  · exact a_reference68_checked
  · exact r_fixed68_linked
  · exact a_fixed68_linked
  · exact time68_checked
  · exact ht
  · exact hw
theorem child_geometry68_checked : ReferenceWeightData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights68 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0017.cert136∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch17_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0017.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0017.cert137∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch17_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0017.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0017.cert136.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry68_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights136_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0017.cert137.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry68_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry68_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights137_linked j (List.mem_finRange j))
theorem actual_frozen_frame68 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame68 (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.flow.timeParameter_mem child_geometry68_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights68 hz)
theorem r_profile69_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r69=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds := by rfl
theorem a_profile69_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a69=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a69.bounds := by rfl
theorem r_fixed69_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 7 := by decide +kernel
theorem a_fixed69_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a69.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.a69.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 9 := by decide +kernel
theorem ranks69_linked : ReferenceRankData.CoarseLowerShape.Batch0008.targetR69=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0008.targetA69=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 1 := by decide +kernel
theorem r_input69_linked : ReferenceRankData.CoarseLowerShape.Batch0008.r69.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds.gauge] := by decide +kernel
theorem a_input69_linked : ReferenceRankData.CoarseLowerShape.Batch0008.a69.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.a69.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.a69.bounds.gauge] := by decide +kernel
theorem geometry69_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.a := by decide +kernel
theorem weights138_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0017.cert138.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights139_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0017.cert139.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time69_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 10)=true := by decide +kernel
theorem r_reference69_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 0)=true := by decide +kernel
theorem a_reference69_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 1)=true := by decide +kernel
theorem rank_r_link69_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r69 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link69_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0008.a69.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a69 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints69 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell true ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r69 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile69_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link69_checked
    geometry69_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell false ReferenceProfileData.CoarseLowerShape.Batch0008.a69.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a69 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile69_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link69_checked
    geometry69_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks69_linked.1,←ranks69_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0008.r69.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a69.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0008.ordered69_checked hr ha ho
theorem frozen_frame69 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69 ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds ReferenceProfileData.CoarseLowerShape.Batch0008.a69.bounds
  · rw [←r_profile69_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile69_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry69_linked.2.2.2.2.1
  · exact geometry69_linked.2.2.2.2.2
  · exact r_reference69_checked
  · exact a_reference69_checked
  · exact r_fixed69_linked
  · exact a_fixed69_linked
  · exact time69_checked
  · exact ht
  · exact hw
theorem child_geometry69_checked : ReferenceWeightData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights69 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0017.cert138∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch17_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0017.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0017.cert139∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch17_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0017.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0017.cert138.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry69_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights138_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0017.cert139.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry69_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry69_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights139_linked j (List.mem_finRange j))
theorem actual_frozen_frame69 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame69 (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.flow.timeParameter_mem child_geometry69_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights69 hz)
theorem r_profile70_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r70=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds := by rfl
theorem a_profile70_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a70=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a70.bounds := by rfl
theorem r_fixed70_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 7 := by decide +kernel
theorem a_fixed70_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a70.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.a70.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 9 := by decide +kernel
theorem ranks70_linked : ReferenceRankData.CoarseLowerShape.Batch0008.targetR70=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0008.targetA70=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 1 := by decide +kernel
theorem r_input70_linked : ReferenceRankData.CoarseLowerShape.Batch0008.r70.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds.gauge] := by decide +kernel
theorem a_input70_linked : ReferenceRankData.CoarseLowerShape.Batch0008.a70.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.a70.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.a70.bounds.gauge] := by decide +kernel
theorem geometry70_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.a := by decide +kernel
theorem weights140_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0017.cert140.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights141_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0017.cert141.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time70_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 10)=true := by decide +kernel
theorem r_reference70_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 0)=true := by decide +kernel
theorem a_reference70_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 1)=true := by decide +kernel
theorem rank_r_link70_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r70 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link70_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0008.a70.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a70 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints70 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell true ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r70 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile70_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link70_checked
    geometry70_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell false ReferenceProfileData.CoarseLowerShape.Batch0008.a70.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a70 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile70_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link70_checked
    geometry70_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks70_linked.1,←ranks70_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0008.r70.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a70.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0008.ordered70_checked hr ha ho
theorem frozen_frame70 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70 ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds ReferenceProfileData.CoarseLowerShape.Batch0008.a70.bounds
  · rw [←r_profile70_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile70_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry70_linked.2.2.2.2.1
  · exact geometry70_linked.2.2.2.2.2
  · exact r_reference70_checked
  · exact a_reference70_checked
  · exact r_fixed70_linked
  · exact a_fixed70_linked
  · exact time70_checked
  · exact ht
  · exact hw
theorem child_geometry70_checked : ReferenceWeightData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights70 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0017.cert140∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch17_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0017.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0017.cert141∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch17_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0017.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0017.cert140.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry70_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights140_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0017.cert141.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry70_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry70_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights141_linked j (List.mem_finRange j))
theorem actual_frozen_frame70 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame70 (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.flow.timeParameter_mem child_geometry70_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights70 hz)
theorem r_profile71_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r71=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds := by rfl
theorem a_profile71_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a71=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a71.bounds := by rfl
theorem r_fixed71_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 7 := by decide +kernel
theorem a_fixed71_linked : ReferenceProfileData.CoarseLowerShape.Batch0008.a71.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0008.a71.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 9 := by decide +kernel
theorem ranks71_linked : ReferenceRankData.CoarseLowerShape.Batch0008.targetR71=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0008.targetA71=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 1 := by decide +kernel
theorem r_input71_linked : ReferenceRankData.CoarseLowerShape.Batch0008.r71.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds.gauge] := by decide +kernel
theorem a_input71_linked : ReferenceRankData.CoarseLowerShape.Batch0008.a71.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0008.a71.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0008.a71.bounds.gauge] := by decide +kernel
theorem geometry71_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.a := by decide +kernel
theorem weights142_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0017.cert142.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights143_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0017.cert143.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time71_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 10)=true := by decide +kernel
theorem r_reference71_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 0)=true := by decide +kernel
theorem a_reference71_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 1)=true := by decide +kernel
theorem rank_r_link71_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r71 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link71_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0008.a71.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a71 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints71 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell true ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds ReferenceRankData.CoarseLowerShape.Batch0008.r71 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile71_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link71_checked
    geometry71_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell false ReferenceProfileData.CoarseLowerShape.Batch0008.a71.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a71 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile71_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0008.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0008.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link71_checked
    geometry71_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks71_linked.1,←ranks71_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0008.r71.bounds ReferenceRankData.CoarseLowerShape.Batch0008.a71.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0008.ordered71_checked hr ha ho
theorem frozen_frame71 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71 ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds ReferenceProfileData.CoarseLowerShape.Batch0008.a71.bounds
  · rw [←r_profile71_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile71_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry71_linked.2.2.2.2.1
  · exact geometry71_linked.2.2.2.2.2
  · exact r_reference71_checked
  · exact a_reference71_checked
  · exact r_fixed71_linked
  · exact a_fixed71_linked
  · exact time71_checked
  · exact ht
  · exact hw
theorem child_geometry71_checked : ReferenceWeightData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights71 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0017.cert142∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch17_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0017.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0017.cert143∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch17_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0017.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0017.cert142.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry71_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights142_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0017.cert143.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry71_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry71_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights143_linked j (List.mem_finRange j))
theorem actual_frozen_frame71 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame71 (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.flow.timeParameter_mem child_geometry71_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights71 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell64),(ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell65),(ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell66),(ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell67),(ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell68),(ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell69),(ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell70),(ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0008.cell71)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0008.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0008.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame64 hz
  · exact fun z hz=>actual_frozen_frame65 hz
  · exact fun z hz=>actual_frozen_frame66 hz
  · exact fun z hz=>actual_frozen_frame67 hz
  · exact fun z hz=>actual_frozen_frame68 hz
  · exact fun z hz=>actual_frozen_frame69 hz
  · exact fun z hz=>actual_frozen_frame70 hz
  · exact fun z hz=>actual_frozen_frame71 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints64 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints65 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints66 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints67 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints68 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints69 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints70 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints71 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry64_linked.1,geometry64_linked.2.1,geometry64_linked.2.2.1,geometry64_linked.2.2.2.1⟩
  · exact ⟨geometry65_linked.1,geometry65_linked.2.1,geometry65_linked.2.2.1,geometry65_linked.2.2.2.1⟩
  · exact ⟨geometry66_linked.1,geometry66_linked.2.1,geometry66_linked.2.2.1,geometry66_linked.2.2.2.1⟩
  · exact ⟨geometry67_linked.1,geometry67_linked.2.1,geometry67_linked.2.2.1,geometry67_linked.2.2.2.1⟩
  · exact ⟨geometry68_linked.1,geometry68_linked.2.1,geometry68_linked.2.2.1,geometry68_linked.2.2.2.1⟩
  · exact ⟨geometry69_linked.1,geometry69_linked.2.1,geometry69_linked.2.2.1,geometry69_linked.2.2.2.1⟩
  · exact ⟨geometry70_linked.1,geometry70_linked.2.1,geometry70_linked.2.2.1,geometry70_linked.2.2.2.1⟩
  · exact ⟨geometry71_linked.1,geometry71_linked.2.1,geometry71_linked.2.2.1,geometry71_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.a64.bounds,?_,geometry64_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a64.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile64_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds,?_,geometry64_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert64.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r64.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile64_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.a65.bounds,?_,geometry65_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a65.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile65_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds,?_,geometry65_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert65.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r65.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile65_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.a66.bounds,?_,geometry66_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a66.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile66_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds,?_,geometry66_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert66.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r66.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile66_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.a67.bounds,?_,geometry67_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a67.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile67_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds,?_,geometry67_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert67.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r67.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile67_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.a68.bounds,?_,geometry68_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a68.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile68_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds,?_,geometry68_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert68.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r68.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile68_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.a69.bounds,?_,geometry69_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a69.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile69_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds,?_,geometry69_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert69.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r69.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile69_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.a70.bounds,?_,geometry70_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a70.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile70_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds,?_,geometry70_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert70.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r70.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile70_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.a71.bounds,?_,geometry71_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0008.a71.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile71_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds,?_,geometry71_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0008.cert71.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0008.r71.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile71_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0008.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0008.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0008

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0009
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch18_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0018.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0018.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch19_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0019.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0019.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile72_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r72=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds := by rfl
theorem a_profile72_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a72=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a72.bounds := by rfl
theorem r_fixed72_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 7 := by decide +kernel
theorem a_fixed72_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a72.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.a72.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 9 := by decide +kernel
theorem ranks72_linked : ReferenceRankData.CoarseLowerShape.Batch0009.targetR72=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0009.targetA72=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 1 := by decide +kernel
theorem r_input72_linked : ReferenceRankData.CoarseLowerShape.Batch0009.r72.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds.gauge] := by decide +kernel
theorem a_input72_linked : ReferenceRankData.CoarseLowerShape.Batch0009.a72.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.a72.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.a72.bounds.gauge] := by decide +kernel
theorem geometry72_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.a := by decide +kernel
theorem weights144_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0018.cert144.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights145_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0018.cert145.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time72_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 10)=true := by decide +kernel
theorem r_reference72_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 0)=true := by decide +kernel
theorem a_reference72_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 1)=true := by decide +kernel
theorem rank_r_link72_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r72 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link72_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0009.a72.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a72 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints72 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell true ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r72 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile72_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link72_checked
    geometry72_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell false ReferenceProfileData.CoarseLowerShape.Batch0009.a72.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a72 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile72_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link72_checked
    geometry72_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks72_linked.1,←ranks72_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0009.r72.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a72.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0009.ordered72_checked hr ha ho
theorem frozen_frame72 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72 ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds ReferenceProfileData.CoarseLowerShape.Batch0009.a72.bounds
  · rw [←r_profile72_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile72_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry72_linked.2.2.2.2.1
  · exact geometry72_linked.2.2.2.2.2
  · exact r_reference72_checked
  · exact a_reference72_checked
  · exact r_fixed72_linked
  · exact a_fixed72_linked
  · exact time72_checked
  · exact ht
  · exact hw
theorem child_geometry72_checked : ReferenceWeightData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights72 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0018.cert144∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch18_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0018.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0018.cert145∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch18_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0018.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0018.cert144.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry72_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights144_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0018.cert145.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry72_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry72_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights145_linked j (List.mem_finRange j))
theorem actual_frozen_frame72 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame72 (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.flow.timeParameter_mem child_geometry72_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights72 hz)
theorem r_profile73_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r73=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds := by rfl
theorem a_profile73_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a73=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a73.bounds := by rfl
theorem r_fixed73_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 7 := by decide +kernel
theorem a_fixed73_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a73.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.a73.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 9 := by decide +kernel
theorem ranks73_linked : ReferenceRankData.CoarseLowerShape.Batch0009.targetR73=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0009.targetA73=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 1 := by decide +kernel
theorem r_input73_linked : ReferenceRankData.CoarseLowerShape.Batch0009.r73.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds.gauge] := by decide +kernel
theorem a_input73_linked : ReferenceRankData.CoarseLowerShape.Batch0009.a73.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.a73.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.a73.bounds.gauge] := by decide +kernel
theorem geometry73_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.a := by decide +kernel
theorem weights146_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0018.cert146.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights147_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0018.cert147.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time73_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 10)=true := by decide +kernel
theorem r_reference73_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 0)=true := by decide +kernel
theorem a_reference73_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 1)=true := by decide +kernel
theorem rank_r_link73_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r73 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link73_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0009.a73.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a73 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints73 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell true ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r73 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile73_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link73_checked
    geometry73_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell false ReferenceProfileData.CoarseLowerShape.Batch0009.a73.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a73 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile73_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link73_checked
    geometry73_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks73_linked.1,←ranks73_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0009.r73.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a73.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0009.ordered73_checked hr ha ho
theorem frozen_frame73 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73 ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds ReferenceProfileData.CoarseLowerShape.Batch0009.a73.bounds
  · rw [←r_profile73_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile73_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry73_linked.2.2.2.2.1
  · exact geometry73_linked.2.2.2.2.2
  · exact r_reference73_checked
  · exact a_reference73_checked
  · exact r_fixed73_linked
  · exact a_fixed73_linked
  · exact time73_checked
  · exact ht
  · exact hw
theorem child_geometry73_checked : ReferenceWeightData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights73 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0018.cert146∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch18_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0018.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0018.cert147∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch18_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0018.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0018.cert146.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry73_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights146_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0018.cert147.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry73_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry73_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights147_linked j (List.mem_finRange j))
theorem actual_frozen_frame73 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame73 (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.flow.timeParameter_mem child_geometry73_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights73 hz)
theorem r_profile74_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r74=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds := by rfl
theorem a_profile74_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a74=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a74.bounds := by rfl
theorem r_fixed74_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 7 := by decide +kernel
theorem a_fixed74_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a74.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.a74.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 9 := by decide +kernel
theorem ranks74_linked : ReferenceRankData.CoarseLowerShape.Batch0009.targetR74=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0009.targetA74=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 1 := by decide +kernel
theorem r_input74_linked : ReferenceRankData.CoarseLowerShape.Batch0009.r74.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds.gauge] := by decide +kernel
theorem a_input74_linked : ReferenceRankData.CoarseLowerShape.Batch0009.a74.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.a74.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.a74.bounds.gauge] := by decide +kernel
theorem geometry74_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.a := by decide +kernel
theorem weights148_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0018.cert148.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights149_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0018.cert149.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time74_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 10)=true := by decide +kernel
theorem r_reference74_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 0)=true := by decide +kernel
theorem a_reference74_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 1)=true := by decide +kernel
theorem rank_r_link74_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r74 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link74_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0009.a74.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a74 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints74 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell true ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r74 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile74_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link74_checked
    geometry74_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell false ReferenceProfileData.CoarseLowerShape.Batch0009.a74.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a74 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile74_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link74_checked
    geometry74_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks74_linked.1,←ranks74_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0009.r74.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a74.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0009.ordered74_checked hr ha ho
theorem frozen_frame74 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74 ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds ReferenceProfileData.CoarseLowerShape.Batch0009.a74.bounds
  · rw [←r_profile74_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile74_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry74_linked.2.2.2.2.1
  · exact geometry74_linked.2.2.2.2.2
  · exact r_reference74_checked
  · exact a_reference74_checked
  · exact r_fixed74_linked
  · exact a_fixed74_linked
  · exact time74_checked
  · exact ht
  · exact hw
theorem child_geometry74_checked : ReferenceWeightData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights74 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0018.cert148∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch18_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0018.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0018.cert149∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch18_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0018.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0018.cert148.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry74_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights148_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0018.cert149.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry74_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry74_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights149_linked j (List.mem_finRange j))
theorem actual_frozen_frame74 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame74 (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.flow.timeParameter_mem child_geometry74_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights74 hz)
theorem r_profile75_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r75=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds := by rfl
theorem a_profile75_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a75=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a75.bounds := by rfl
theorem r_fixed75_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 7 := by decide +kernel
theorem a_fixed75_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a75.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.a75.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 9 := by decide +kernel
theorem ranks75_linked : ReferenceRankData.CoarseLowerShape.Batch0009.targetR75=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0009.targetA75=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 1 := by decide +kernel
theorem r_input75_linked : ReferenceRankData.CoarseLowerShape.Batch0009.r75.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds.gauge] := by decide +kernel
theorem a_input75_linked : ReferenceRankData.CoarseLowerShape.Batch0009.a75.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.a75.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.a75.bounds.gauge] := by decide +kernel
theorem geometry75_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.a := by decide +kernel
theorem weights150_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0018.cert150.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights151_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0018.cert151.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time75_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 10)=true := by decide +kernel
theorem r_reference75_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 0)=true := by decide +kernel
theorem a_reference75_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 1)=true := by decide +kernel
theorem rank_r_link75_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r75 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link75_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0009.a75.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a75 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints75 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell true ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r75 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile75_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link75_checked
    geometry75_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell false ReferenceProfileData.CoarseLowerShape.Batch0009.a75.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a75 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile75_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link75_checked
    geometry75_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks75_linked.1,←ranks75_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0009.r75.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a75.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0009.ordered75_checked hr ha ho
theorem frozen_frame75 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75 ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds ReferenceProfileData.CoarseLowerShape.Batch0009.a75.bounds
  · rw [←r_profile75_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile75_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry75_linked.2.2.2.2.1
  · exact geometry75_linked.2.2.2.2.2
  · exact r_reference75_checked
  · exact a_reference75_checked
  · exact r_fixed75_linked
  · exact a_fixed75_linked
  · exact time75_checked
  · exact ht
  · exact hw
theorem child_geometry75_checked : ReferenceWeightData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights75 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0018.cert150∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch18_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0018.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0018.cert151∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch18_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0018.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0018.cert150.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry75_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights150_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0018.cert151.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry75_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry75_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights151_linked j (List.mem_finRange j))
theorem actual_frozen_frame75 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame75 (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.flow.timeParameter_mem child_geometry75_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights75 hz)
theorem r_profile76_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r76=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds := by rfl
theorem a_profile76_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a76=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a76.bounds := by rfl
theorem r_fixed76_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 7 := by decide +kernel
theorem a_fixed76_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a76.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.a76.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 9 := by decide +kernel
theorem ranks76_linked : ReferenceRankData.CoarseLowerShape.Batch0009.targetR76=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0009.targetA76=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 1 := by decide +kernel
theorem r_input76_linked : ReferenceRankData.CoarseLowerShape.Batch0009.r76.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds.gauge] := by decide +kernel
theorem a_input76_linked : ReferenceRankData.CoarseLowerShape.Batch0009.a76.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.a76.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.a76.bounds.gauge] := by decide +kernel
theorem geometry76_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.a := by decide +kernel
theorem weights152_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0019.cert152.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights153_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0019.cert153.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time76_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 10)=true := by decide +kernel
theorem r_reference76_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 0)=true := by decide +kernel
theorem a_reference76_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 1)=true := by decide +kernel
theorem rank_r_link76_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r76 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link76_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0009.a76.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a76 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints76 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell true ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r76 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile76_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link76_checked
    geometry76_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell false ReferenceProfileData.CoarseLowerShape.Batch0009.a76.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a76 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile76_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link76_checked
    geometry76_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks76_linked.1,←ranks76_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0009.r76.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a76.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0009.ordered76_checked hr ha ho
theorem frozen_frame76 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76 ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds ReferenceProfileData.CoarseLowerShape.Batch0009.a76.bounds
  · rw [←r_profile76_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile76_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry76_linked.2.2.2.2.1
  · exact geometry76_linked.2.2.2.2.2
  · exact r_reference76_checked
  · exact a_reference76_checked
  · exact r_fixed76_linked
  · exact a_fixed76_linked
  · exact time76_checked
  · exact ht
  · exact hw
theorem child_geometry76_checked : ReferenceWeightData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights76 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0019.cert152∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch19_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0019.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0019.cert153∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch19_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0019.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0019.cert152.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry76_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights152_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0019.cert153.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry76_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry76_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights153_linked j (List.mem_finRange j))
theorem actual_frozen_frame76 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame76 (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.flow.timeParameter_mem child_geometry76_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights76 hz)
theorem r_profile77_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r77=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds := by rfl
theorem a_profile77_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a77=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a77.bounds := by rfl
theorem r_fixed77_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 7 := by decide +kernel
theorem a_fixed77_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a77.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.a77.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 9 := by decide +kernel
theorem ranks77_linked : ReferenceRankData.CoarseLowerShape.Batch0009.targetR77=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0009.targetA77=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 1 := by decide +kernel
theorem r_input77_linked : ReferenceRankData.CoarseLowerShape.Batch0009.r77.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds.gauge] := by decide +kernel
theorem a_input77_linked : ReferenceRankData.CoarseLowerShape.Batch0009.a77.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.a77.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.a77.bounds.gauge] := by decide +kernel
theorem geometry77_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.a := by decide +kernel
theorem weights154_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0019.cert154.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights155_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0019.cert155.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time77_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 10)=true := by decide +kernel
theorem r_reference77_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 0)=true := by decide +kernel
theorem a_reference77_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 1)=true := by decide +kernel
theorem rank_r_link77_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r77 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link77_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0009.a77.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a77 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints77 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell true ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r77 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile77_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link77_checked
    geometry77_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell false ReferenceProfileData.CoarseLowerShape.Batch0009.a77.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a77 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile77_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link77_checked
    geometry77_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks77_linked.1,←ranks77_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0009.r77.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a77.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0009.ordered77_checked hr ha ho
theorem frozen_frame77 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77 ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds ReferenceProfileData.CoarseLowerShape.Batch0009.a77.bounds
  · rw [←r_profile77_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile77_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry77_linked.2.2.2.2.1
  · exact geometry77_linked.2.2.2.2.2
  · exact r_reference77_checked
  · exact a_reference77_checked
  · exact r_fixed77_linked
  · exact a_fixed77_linked
  · exact time77_checked
  · exact ht
  · exact hw
theorem child_geometry77_checked : ReferenceWeightData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights77 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0019.cert154∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch19_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0019.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0019.cert155∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch19_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0019.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0019.cert154.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry77_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights154_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0019.cert155.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry77_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry77_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights155_linked j (List.mem_finRange j))
theorem actual_frozen_frame77 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame77 (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.flow.timeParameter_mem child_geometry77_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights77 hz)
theorem r_profile78_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r78=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds := by rfl
theorem a_profile78_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a78=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a78.bounds := by rfl
theorem r_fixed78_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 7 := by decide +kernel
theorem a_fixed78_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a78.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.a78.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 9 := by decide +kernel
theorem ranks78_linked : ReferenceRankData.CoarseLowerShape.Batch0009.targetR78=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0009.targetA78=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 1 := by decide +kernel
theorem r_input78_linked : ReferenceRankData.CoarseLowerShape.Batch0009.r78.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds.gauge] := by decide +kernel
theorem a_input78_linked : ReferenceRankData.CoarseLowerShape.Batch0009.a78.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.a78.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.a78.bounds.gauge] := by decide +kernel
theorem geometry78_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.a := by decide +kernel
theorem weights156_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0019.cert156.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights157_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0019.cert157.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time78_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 10)=true := by decide +kernel
theorem r_reference78_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 0)=true := by decide +kernel
theorem a_reference78_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 1)=true := by decide +kernel
theorem rank_r_link78_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r78 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link78_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0009.a78.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a78 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints78 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell true ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r78 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile78_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link78_checked
    geometry78_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell false ReferenceProfileData.CoarseLowerShape.Batch0009.a78.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a78 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile78_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link78_checked
    geometry78_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks78_linked.1,←ranks78_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0009.r78.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a78.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0009.ordered78_checked hr ha ho
theorem frozen_frame78 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78 ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds ReferenceProfileData.CoarseLowerShape.Batch0009.a78.bounds
  · rw [←r_profile78_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile78_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry78_linked.2.2.2.2.1
  · exact geometry78_linked.2.2.2.2.2
  · exact r_reference78_checked
  · exact a_reference78_checked
  · exact r_fixed78_linked
  · exact a_fixed78_linked
  · exact time78_checked
  · exact ht
  · exact hw
theorem child_geometry78_checked : ReferenceWeightData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights78 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0019.cert156∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch19_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0019.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0019.cert157∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch19_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0019.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0019.cert156.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry78_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights156_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0019.cert157.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry78_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry78_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights157_linked j (List.mem_finRange j))
theorem actual_frozen_frame78 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame78 (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.flow.timeParameter_mem child_geometry78_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights78 hz)
theorem r_profile79_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r79=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds := by rfl
theorem a_profile79_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a79=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a79.bounds := by rfl
theorem r_fixed79_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 7 := by decide +kernel
theorem a_fixed79_linked : ReferenceProfileData.CoarseLowerShape.Batch0009.a79.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0009.a79.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 9 := by decide +kernel
theorem ranks79_linked : ReferenceRankData.CoarseLowerShape.Batch0009.targetR79=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0009.targetA79=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 1 := by decide +kernel
theorem r_input79_linked : ReferenceRankData.CoarseLowerShape.Batch0009.r79.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds.gauge] := by decide +kernel
theorem a_input79_linked : ReferenceRankData.CoarseLowerShape.Batch0009.a79.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0009.a79.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0009.a79.bounds.gauge] := by decide +kernel
theorem geometry79_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.a := by decide +kernel
theorem weights158_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0019.cert158.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights159_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0019.cert159.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time79_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 10)=true := by decide +kernel
theorem r_reference79_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 0)=true := by decide +kernel
theorem a_reference79_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 1)=true := by decide +kernel
theorem rank_r_link79_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r79 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link79_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0009.a79.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a79 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints79 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell true ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds ReferenceRankData.CoarseLowerShape.Batch0009.r79 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile79_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link79_checked
    geometry79_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell false ReferenceProfileData.CoarseLowerShape.Batch0009.a79.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a79 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile79_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0009.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0009.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link79_checked
    geometry79_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks79_linked.1,←ranks79_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0009.r79.bounds ReferenceRankData.CoarseLowerShape.Batch0009.a79.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0009.ordered79_checked hr ha ho
theorem frozen_frame79 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79 ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds ReferenceProfileData.CoarseLowerShape.Batch0009.a79.bounds
  · rw [←r_profile79_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile79_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry79_linked.2.2.2.2.1
  · exact geometry79_linked.2.2.2.2.2
  · exact r_reference79_checked
  · exact a_reference79_checked
  · exact r_fixed79_linked
  · exact a_fixed79_linked
  · exact time79_checked
  · exact ht
  · exact hw
theorem child_geometry79_checked : ReferenceWeightData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights79 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0019.cert158∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch19_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0019.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0019.cert159∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch19_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0019.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0019.cert158.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry79_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights158_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0019.cert159.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry79_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry79_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights159_linked j (List.mem_finRange j))
theorem actual_frozen_frame79 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame79 (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.flow.timeParameter_mem child_geometry79_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights79 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell72),(ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell73),(ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell74),(ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell75),(ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell76),(ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell77),(ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell78),(ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0009.cell79)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0009.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0009.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame72 hz
  · exact fun z hz=>actual_frozen_frame73 hz
  · exact fun z hz=>actual_frozen_frame74 hz
  · exact fun z hz=>actual_frozen_frame75 hz
  · exact fun z hz=>actual_frozen_frame76 hz
  · exact fun z hz=>actual_frozen_frame77 hz
  · exact fun z hz=>actual_frozen_frame78 hz
  · exact fun z hz=>actual_frozen_frame79 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints72 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints73 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints74 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints75 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints76 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints77 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints78 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints79 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry72_linked.1,geometry72_linked.2.1,geometry72_linked.2.2.1,geometry72_linked.2.2.2.1⟩
  · exact ⟨geometry73_linked.1,geometry73_linked.2.1,geometry73_linked.2.2.1,geometry73_linked.2.2.2.1⟩
  · exact ⟨geometry74_linked.1,geometry74_linked.2.1,geometry74_linked.2.2.1,geometry74_linked.2.2.2.1⟩
  · exact ⟨geometry75_linked.1,geometry75_linked.2.1,geometry75_linked.2.2.1,geometry75_linked.2.2.2.1⟩
  · exact ⟨geometry76_linked.1,geometry76_linked.2.1,geometry76_linked.2.2.1,geometry76_linked.2.2.2.1⟩
  · exact ⟨geometry77_linked.1,geometry77_linked.2.1,geometry77_linked.2.2.1,geometry77_linked.2.2.2.1⟩
  · exact ⟨geometry78_linked.1,geometry78_linked.2.1,geometry78_linked.2.2.1,geometry78_linked.2.2.2.1⟩
  · exact ⟨geometry79_linked.1,geometry79_linked.2.1,geometry79_linked.2.2.1,geometry79_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.a72.bounds,?_,geometry72_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a72.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile72_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds,?_,geometry72_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert72.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r72.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile72_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.a73.bounds,?_,geometry73_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a73.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile73_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds,?_,geometry73_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert73.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r73.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile73_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.a74.bounds,?_,geometry74_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a74.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile74_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds,?_,geometry74_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert74.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r74.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile74_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.a75.bounds,?_,geometry75_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a75.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile75_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds,?_,geometry75_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert75.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r75.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile75_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.a76.bounds,?_,geometry76_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a76.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile76_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds,?_,geometry76_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert76.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r76.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile76_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.a77.bounds,?_,geometry77_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a77.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile77_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds,?_,geometry77_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert77.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r77.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile77_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.a78.bounds,?_,geometry78_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a78.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile78_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds,?_,geometry78_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert78.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r78.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile78_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.a79.bounds,?_,geometry79_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0009.a79.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile79_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds,?_,geometry79_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0009.cert79.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0009.r79.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile79_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0009.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0009.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0009

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0010
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch20_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0020.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0020.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch21_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0021.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0021.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile80_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r80=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds := by rfl
theorem a_profile80_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a80=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a80.bounds := by rfl
theorem r_fixed80_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 7 := by decide +kernel
theorem a_fixed80_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a80.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.a80.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 9 := by decide +kernel
theorem ranks80_linked : ReferenceRankData.CoarseLowerShape.Batch0010.targetR80=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0010.targetA80=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 1 := by decide +kernel
theorem r_input80_linked : ReferenceRankData.CoarseLowerShape.Batch0010.r80.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds.gauge] := by decide +kernel
theorem a_input80_linked : ReferenceRankData.CoarseLowerShape.Batch0010.a80.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.a80.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.a80.bounds.gauge] := by decide +kernel
theorem geometry80_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.a := by decide +kernel
theorem weights160_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0020.cert160.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights161_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0020.cert161.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time80_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 10)=true := by decide +kernel
theorem r_reference80_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 0)=true := by decide +kernel
theorem a_reference80_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 1)=true := by decide +kernel
theorem rank_r_link80_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r80 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link80_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0010.a80.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a80 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints80 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell true ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r80 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile80_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link80_checked
    geometry80_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell false ReferenceProfileData.CoarseLowerShape.Batch0010.a80.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a80 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile80_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link80_checked
    geometry80_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks80_linked.1,←ranks80_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0010.r80.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a80.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0010.ordered80_checked hr ha ho
theorem frozen_frame80 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80 ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds ReferenceProfileData.CoarseLowerShape.Batch0010.a80.bounds
  · rw [←r_profile80_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile80_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry80_linked.2.2.2.2.1
  · exact geometry80_linked.2.2.2.2.2
  · exact r_reference80_checked
  · exact a_reference80_checked
  · exact r_fixed80_linked
  · exact a_fixed80_linked
  · exact time80_checked
  · exact ht
  · exact hw
theorem child_geometry80_checked : ReferenceWeightData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights80 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0020.cert160∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch20_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0020.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0020.cert161∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch20_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0020.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry80_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights160_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry80_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry80_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights161_linked j (List.mem_finRange j))
theorem actual_frozen_frame80 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame80 (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.flow.timeParameter_mem child_geometry80_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights80 hz)
theorem r_profile81_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r81=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds := by rfl
theorem a_profile81_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a81=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a81.bounds := by rfl
theorem r_fixed81_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 7 := by decide +kernel
theorem a_fixed81_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a81.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.a81.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 9 := by decide +kernel
theorem ranks81_linked : ReferenceRankData.CoarseLowerShape.Batch0010.targetR81=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0010.targetA81=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 1 := by decide +kernel
theorem r_input81_linked : ReferenceRankData.CoarseLowerShape.Batch0010.r81.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds.gauge] := by decide +kernel
theorem a_input81_linked : ReferenceRankData.CoarseLowerShape.Batch0010.a81.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.a81.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.a81.bounds.gauge] := by decide +kernel
theorem geometry81_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.a := by decide +kernel
theorem weights162_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0020.cert162.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights163_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0020.cert163.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time81_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 10)=true := by decide +kernel
theorem r_reference81_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 0)=true := by decide +kernel
theorem a_reference81_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 1)=true := by decide +kernel
theorem rank_r_link81_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r81 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link81_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0010.a81.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a81 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints81 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell true ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r81 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile81_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link81_checked
    geometry81_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell false ReferenceProfileData.CoarseLowerShape.Batch0010.a81.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a81 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile81_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link81_checked
    geometry81_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks81_linked.1,←ranks81_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0010.r81.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a81.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0010.ordered81_checked hr ha ho
theorem frozen_frame81 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81 ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds ReferenceProfileData.CoarseLowerShape.Batch0010.a81.bounds
  · rw [←r_profile81_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile81_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry81_linked.2.2.2.2.1
  · exact geometry81_linked.2.2.2.2.2
  · exact r_reference81_checked
  · exact a_reference81_checked
  · exact r_fixed81_linked
  · exact a_fixed81_linked
  · exact time81_checked
  · exact ht
  · exact hw
theorem child_geometry81_checked : ReferenceWeightData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights81 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0020.cert162∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch20_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0020.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0020.cert163∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch20_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0020.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry81_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights162_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry81_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry81_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights163_linked j (List.mem_finRange j))
theorem actual_frozen_frame81 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame81 (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.flow.timeParameter_mem child_geometry81_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights81 hz)
theorem r_profile82_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r82=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds := by rfl
theorem a_profile82_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a82=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a82.bounds := by rfl
theorem r_fixed82_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 7 := by decide +kernel
theorem a_fixed82_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a82.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.a82.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 9 := by decide +kernel
theorem ranks82_linked : ReferenceRankData.CoarseLowerShape.Batch0010.targetR82=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0010.targetA82=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 1 := by decide +kernel
theorem r_input82_linked : ReferenceRankData.CoarseLowerShape.Batch0010.r82.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds.gauge] := by decide +kernel
theorem a_input82_linked : ReferenceRankData.CoarseLowerShape.Batch0010.a82.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.a82.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.a82.bounds.gauge] := by decide +kernel
theorem geometry82_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.a := by decide +kernel
theorem weights164_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0020.cert164.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights165_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0020.cert165.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time82_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 10)=true := by decide +kernel
theorem r_reference82_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 0)=true := by decide +kernel
theorem a_reference82_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 1)=true := by decide +kernel
theorem rank_r_link82_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r82 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link82_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0010.a82.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a82 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints82 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell true ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r82 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile82_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link82_checked
    geometry82_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell false ReferenceProfileData.CoarseLowerShape.Batch0010.a82.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a82 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile82_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link82_checked
    geometry82_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks82_linked.1,←ranks82_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0010.r82.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a82.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0010.ordered82_checked hr ha ho
theorem frozen_frame82 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82 ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds ReferenceProfileData.CoarseLowerShape.Batch0010.a82.bounds
  · rw [←r_profile82_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile82_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry82_linked.2.2.2.2.1
  · exact geometry82_linked.2.2.2.2.2
  · exact r_reference82_checked
  · exact a_reference82_checked
  · exact r_fixed82_linked
  · exact a_fixed82_linked
  · exact time82_checked
  · exact ht
  · exact hw
theorem child_geometry82_checked : ReferenceWeightData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights82 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0020.cert164∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch20_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0020.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0020.cert165∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch20_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0020.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry82_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights164_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry82_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry82_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights165_linked j (List.mem_finRange j))
theorem actual_frozen_frame82 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame82 (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.flow.timeParameter_mem child_geometry82_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights82 hz)
theorem r_profile83_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r83=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds := by rfl
theorem a_profile83_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a83=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a83.bounds := by rfl
theorem r_fixed83_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 7 := by decide +kernel
theorem a_fixed83_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a83.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.a83.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 9 := by decide +kernel
theorem ranks83_linked : ReferenceRankData.CoarseLowerShape.Batch0010.targetR83=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0010.targetA83=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 1 := by decide +kernel
theorem r_input83_linked : ReferenceRankData.CoarseLowerShape.Batch0010.r83.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds.gauge] := by decide +kernel
theorem a_input83_linked : ReferenceRankData.CoarseLowerShape.Batch0010.a83.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.a83.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.a83.bounds.gauge] := by decide +kernel
theorem geometry83_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.a := by decide +kernel
theorem weights166_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0020.cert166.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights167_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0020.cert167.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time83_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 10)=true := by decide +kernel
theorem r_reference83_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 0)=true := by decide +kernel
theorem a_reference83_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 1)=true := by decide +kernel
theorem rank_r_link83_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r83 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link83_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0010.a83.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a83 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints83 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell true ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r83 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile83_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link83_checked
    geometry83_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell false ReferenceProfileData.CoarseLowerShape.Batch0010.a83.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a83 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile83_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link83_checked
    geometry83_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks83_linked.1,←ranks83_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0010.r83.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a83.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0010.ordered83_checked hr ha ho
theorem frozen_frame83 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83 ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds ReferenceProfileData.CoarseLowerShape.Batch0010.a83.bounds
  · rw [←r_profile83_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile83_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry83_linked.2.2.2.2.1
  · exact geometry83_linked.2.2.2.2.2
  · exact r_reference83_checked
  · exact a_reference83_checked
  · exact r_fixed83_linked
  · exact a_fixed83_linked
  · exact time83_checked
  · exact ht
  · exact hw
theorem child_geometry83_checked : ReferenceWeightData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights83 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0020.cert166∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch20_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0020.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0020.cert167∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch20_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0020.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry83_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights166_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry83_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry83_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights167_linked j (List.mem_finRange j))
theorem actual_frozen_frame83 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame83 (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.flow.timeParameter_mem child_geometry83_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights83 hz)
theorem r_profile84_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r84=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds := by rfl
theorem a_profile84_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a84=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a84.bounds := by rfl
theorem r_fixed84_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 7 := by decide +kernel
theorem a_fixed84_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a84.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.a84.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 9 := by decide +kernel
theorem ranks84_linked : ReferenceRankData.CoarseLowerShape.Batch0010.targetR84=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0010.targetA84=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 1 := by decide +kernel
theorem r_input84_linked : ReferenceRankData.CoarseLowerShape.Batch0010.r84.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds.gauge] := by decide +kernel
theorem a_input84_linked : ReferenceRankData.CoarseLowerShape.Batch0010.a84.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.a84.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.a84.bounds.gauge] := by decide +kernel
theorem geometry84_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.a := by decide +kernel
theorem weights168_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0021.cert168.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights169_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0021.cert169.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time84_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 10)=true := by decide +kernel
theorem r_reference84_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 0)=true := by decide +kernel
theorem a_reference84_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 1)=true := by decide +kernel
theorem rank_r_link84_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r84 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link84_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0010.a84.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a84 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints84 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell true ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r84 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile84_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link84_checked
    geometry84_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell false ReferenceProfileData.CoarseLowerShape.Batch0010.a84.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a84 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile84_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link84_checked
    geometry84_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks84_linked.1,←ranks84_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0010.r84.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a84.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0010.ordered84_checked hr ha ho
theorem frozen_frame84 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84 ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds ReferenceProfileData.CoarseLowerShape.Batch0010.a84.bounds
  · rw [←r_profile84_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile84_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry84_linked.2.2.2.2.1
  · exact geometry84_linked.2.2.2.2.2
  · exact r_reference84_checked
  · exact a_reference84_checked
  · exact r_fixed84_linked
  · exact a_fixed84_linked
  · exact time84_checked
  · exact ht
  · exact hw
theorem child_geometry84_checked : ReferenceWeightData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights84 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0021.cert168∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch21_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0021.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0021.cert169∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch21_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0021.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry84_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights168_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry84_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry84_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights169_linked j (List.mem_finRange j))
theorem actual_frozen_frame84 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame84 (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.flow.timeParameter_mem child_geometry84_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights84 hz)
theorem r_profile85_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r85=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds := by rfl
theorem a_profile85_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a85=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a85.bounds := by rfl
theorem r_fixed85_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 7 := by decide +kernel
theorem a_fixed85_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a85.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.a85.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 9 := by decide +kernel
theorem ranks85_linked : ReferenceRankData.CoarseLowerShape.Batch0010.targetR85=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0010.targetA85=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 1 := by decide +kernel
theorem r_input85_linked : ReferenceRankData.CoarseLowerShape.Batch0010.r85.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds.gauge] := by decide +kernel
theorem a_input85_linked : ReferenceRankData.CoarseLowerShape.Batch0010.a85.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.a85.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.a85.bounds.gauge] := by decide +kernel
theorem geometry85_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.a := by decide +kernel
theorem weights170_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0021.cert170.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights171_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0021.cert171.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time85_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 10)=true := by decide +kernel
theorem r_reference85_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 0)=true := by decide +kernel
theorem a_reference85_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 1)=true := by decide +kernel
theorem rank_r_link85_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r85 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link85_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0010.a85.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a85 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints85 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell true ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r85 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile85_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link85_checked
    geometry85_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell false ReferenceProfileData.CoarseLowerShape.Batch0010.a85.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a85 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile85_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link85_checked
    geometry85_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks85_linked.1,←ranks85_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0010.r85.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a85.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0010.ordered85_checked hr ha ho
theorem frozen_frame85 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85 ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds ReferenceProfileData.CoarseLowerShape.Batch0010.a85.bounds
  · rw [←r_profile85_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile85_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry85_linked.2.2.2.2.1
  · exact geometry85_linked.2.2.2.2.2
  · exact r_reference85_checked
  · exact a_reference85_checked
  · exact r_fixed85_linked
  · exact a_fixed85_linked
  · exact time85_checked
  · exact ht
  · exact hw
theorem child_geometry85_checked : ReferenceWeightData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights85 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0021.cert170∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch21_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0021.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0021.cert171∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch21_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0021.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry85_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights170_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry85_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry85_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights171_linked j (List.mem_finRange j))
theorem actual_frozen_frame85 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame85 (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.flow.timeParameter_mem child_geometry85_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights85 hz)
theorem r_profile86_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r86=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds := by rfl
theorem a_profile86_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a86=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a86.bounds := by rfl
theorem r_fixed86_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 7 := by decide +kernel
theorem a_fixed86_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a86.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.a86.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 9 := by decide +kernel
theorem ranks86_linked : ReferenceRankData.CoarseLowerShape.Batch0010.targetR86=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0010.targetA86=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 1 := by decide +kernel
theorem r_input86_linked : ReferenceRankData.CoarseLowerShape.Batch0010.r86.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds.gauge] := by decide +kernel
theorem a_input86_linked : ReferenceRankData.CoarseLowerShape.Batch0010.a86.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.a86.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.a86.bounds.gauge] := by decide +kernel
theorem geometry86_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.a := by decide +kernel
theorem weights172_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0021.cert172.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights173_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0021.cert173.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time86_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 10)=true := by decide +kernel
theorem r_reference86_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 0)=true := by decide +kernel
theorem a_reference86_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 1)=true := by decide +kernel
theorem rank_r_link86_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r86 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link86_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0010.a86.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a86 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints86 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell true ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r86 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile86_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link86_checked
    geometry86_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell false ReferenceProfileData.CoarseLowerShape.Batch0010.a86.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a86 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile86_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link86_checked
    geometry86_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks86_linked.1,←ranks86_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0010.r86.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a86.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0010.ordered86_checked hr ha ho
theorem frozen_frame86 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86 ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds ReferenceProfileData.CoarseLowerShape.Batch0010.a86.bounds
  · rw [←r_profile86_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile86_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry86_linked.2.2.2.2.1
  · exact geometry86_linked.2.2.2.2.2
  · exact r_reference86_checked
  · exact a_reference86_checked
  · exact r_fixed86_linked
  · exact a_fixed86_linked
  · exact time86_checked
  · exact ht
  · exact hw
theorem child_geometry86_checked : ReferenceWeightData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights86 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0021.cert172∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch21_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0021.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0021.cert173∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch21_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0021.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry86_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights172_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry86_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry86_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights173_linked j (List.mem_finRange j))
theorem actual_frozen_frame86 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame86 (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.flow.timeParameter_mem child_geometry86_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights86 hz)
theorem r_profile87_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r87=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds := by rfl
theorem a_profile87_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a87=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a87.bounds := by rfl
theorem r_fixed87_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 7 := by decide +kernel
theorem a_fixed87_linked : ReferenceProfileData.CoarseLowerShape.Batch0010.a87.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0010.a87.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 9 := by decide +kernel
theorem ranks87_linked : ReferenceRankData.CoarseLowerShape.Batch0010.targetR87=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0010.targetA87=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 1 := by decide +kernel
theorem r_input87_linked : ReferenceRankData.CoarseLowerShape.Batch0010.r87.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds.gauge] := by decide +kernel
theorem a_input87_linked : ReferenceRankData.CoarseLowerShape.Batch0010.a87.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0010.a87.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0010.a87.bounds.gauge] := by decide +kernel
theorem geometry87_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.a := by decide +kernel
theorem weights174_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0021.cert174.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights175_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0021.cert175.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time87_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 10)=true := by decide +kernel
theorem r_reference87_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 0)=true := by decide +kernel
theorem a_reference87_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 1)=true := by decide +kernel
theorem rank_r_link87_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r87 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link87_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0010.a87.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a87 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints87 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell true ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds ReferenceRankData.CoarseLowerShape.Batch0010.r87 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile87_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link87_checked
    geometry87_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell false ReferenceProfileData.CoarseLowerShape.Batch0010.a87.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a87 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile87_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0010.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0010.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link87_checked
    geometry87_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks87_linked.1,←ranks87_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0010.r87.bounds ReferenceRankData.CoarseLowerShape.Batch0010.a87.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0010.ordered87_checked hr ha ho
theorem frozen_frame87 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87 ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds ReferenceProfileData.CoarseLowerShape.Batch0010.a87.bounds
  · rw [←r_profile87_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile87_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry87_linked.2.2.2.2.1
  · exact geometry87_linked.2.2.2.2.2
  · exact r_reference87_checked
  · exact a_reference87_checked
  · exact r_fixed87_linked
  · exact a_fixed87_linked
  · exact time87_checked
  · exact ht
  · exact hw
theorem child_geometry87_checked : ReferenceWeightData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights87 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0021.cert174∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch21_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0021.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0021.cert175∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch21_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0021.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry87_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights174_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry87_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry87_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights175_linked j (List.mem_finRange j))
theorem actual_frozen_frame87 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame87 (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.flow.timeParameter_mem child_geometry87_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights87 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell80),(ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell81),(ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell82),(ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell83),(ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell84),(ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell85),(ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell86),(ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0010.cell87)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0010.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0010.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame80 hz
  · exact fun z hz=>actual_frozen_frame81 hz
  · exact fun z hz=>actual_frozen_frame82 hz
  · exact fun z hz=>actual_frozen_frame83 hz
  · exact fun z hz=>actual_frozen_frame84 hz
  · exact fun z hz=>actual_frozen_frame85 hz
  · exact fun z hz=>actual_frozen_frame86 hz
  · exact fun z hz=>actual_frozen_frame87 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints80 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints81 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints82 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints83 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints84 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints85 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints86 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints87 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry80_linked.1,geometry80_linked.2.1,geometry80_linked.2.2.1,geometry80_linked.2.2.2.1⟩
  · exact ⟨geometry81_linked.1,geometry81_linked.2.1,geometry81_linked.2.2.1,geometry81_linked.2.2.2.1⟩
  · exact ⟨geometry82_linked.1,geometry82_linked.2.1,geometry82_linked.2.2.1,geometry82_linked.2.2.2.1⟩
  · exact ⟨geometry83_linked.1,geometry83_linked.2.1,geometry83_linked.2.2.1,geometry83_linked.2.2.2.1⟩
  · exact ⟨geometry84_linked.1,geometry84_linked.2.1,geometry84_linked.2.2.1,geometry84_linked.2.2.2.1⟩
  · exact ⟨geometry85_linked.1,geometry85_linked.2.1,geometry85_linked.2.2.1,geometry85_linked.2.2.2.1⟩
  · exact ⟨geometry86_linked.1,geometry86_linked.2.1,geometry86_linked.2.2.1,geometry86_linked.2.2.2.1⟩
  · exact ⟨geometry87_linked.1,geometry87_linked.2.1,geometry87_linked.2.2.1,geometry87_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.a80.bounds,?_,geometry80_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a80.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile80_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds,?_,geometry80_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert80.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r80.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile80_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.a81.bounds,?_,geometry81_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a81.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile81_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds,?_,geometry81_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert81.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r81.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile81_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.a82.bounds,?_,geometry82_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a82.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile82_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds,?_,geometry82_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert82.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r82.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile82_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.a83.bounds,?_,geometry83_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a83.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile83_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds,?_,geometry83_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert83.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r83.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile83_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.a84.bounds,?_,geometry84_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a84.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile84_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds,?_,geometry84_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert84.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r84.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile84_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.a85.bounds,?_,geometry85_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a85.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile85_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds,?_,geometry85_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert85.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r85.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile85_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.a86.bounds,?_,geometry86_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a86.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile86_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds,?_,geometry86_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert86.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r86.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile86_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.a87.bounds,?_,geometry87_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0010.a87.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile87_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds,?_,geometry87_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0010.cert87.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0010.r87.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile87_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0010.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0010.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0010

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0011
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch22_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0022.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0022.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch23_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0023.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0023.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile88_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r88=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds := by rfl
theorem a_profile88_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a88=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a88.bounds := by rfl
theorem r_fixed88_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 7 := by decide +kernel
theorem a_fixed88_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a88.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.a88.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 9 := by decide +kernel
theorem ranks88_linked : ReferenceRankData.CoarseLowerShape.Batch0011.targetR88=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0011.targetA88=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 1 := by decide +kernel
theorem r_input88_linked : ReferenceRankData.CoarseLowerShape.Batch0011.r88.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds.gauge] := by decide +kernel
theorem a_input88_linked : ReferenceRankData.CoarseLowerShape.Batch0011.a88.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.a88.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.a88.bounds.gauge] := by decide +kernel
theorem geometry88_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.a := by decide +kernel
theorem weights176_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0022.cert176.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights177_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0022.cert177.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time88_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 10)=true := by decide +kernel
theorem r_reference88_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 0)=true := by decide +kernel
theorem a_reference88_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 1)=true := by decide +kernel
theorem rank_r_link88_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r88 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link88_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0011.a88.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a88 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints88 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell true ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r88 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile88_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link88_checked
    geometry88_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell false ReferenceProfileData.CoarseLowerShape.Batch0011.a88.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a88 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile88_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link88_checked
    geometry88_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks88_linked.1,←ranks88_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0011.r88.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a88.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0011.ordered88_checked hr ha ho
theorem frozen_frame88 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88 ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds ReferenceProfileData.CoarseLowerShape.Batch0011.a88.bounds
  · rw [←r_profile88_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile88_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry88_linked.2.2.2.2.1
  · exact geometry88_linked.2.2.2.2.2
  · exact r_reference88_checked
  · exact a_reference88_checked
  · exact r_fixed88_linked
  · exact a_fixed88_linked
  · exact time88_checked
  · exact ht
  · exact hw
theorem child_geometry88_checked : ReferenceWeightData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights88 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0022.cert176∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch22_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0022.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0022.cert177∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch22_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0022.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry88_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights176_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry88_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry88_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights177_linked j (List.mem_finRange j))
theorem actual_frozen_frame88 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame88 (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.flow.timeParameter_mem child_geometry88_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights88 hz)
theorem r_profile89_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r89=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds := by rfl
theorem a_profile89_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a89=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a89.bounds := by rfl
theorem r_fixed89_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 7 := by decide +kernel
theorem a_fixed89_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a89.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.a89.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 9 := by decide +kernel
theorem ranks89_linked : ReferenceRankData.CoarseLowerShape.Batch0011.targetR89=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0011.targetA89=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 1 := by decide +kernel
theorem r_input89_linked : ReferenceRankData.CoarseLowerShape.Batch0011.r89.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds.gauge] := by decide +kernel
theorem a_input89_linked : ReferenceRankData.CoarseLowerShape.Batch0011.a89.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.a89.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.a89.bounds.gauge] := by decide +kernel
theorem geometry89_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.a := by decide +kernel
theorem weights178_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0022.cert178.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights179_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0022.cert179.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time89_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 10)=true := by decide +kernel
theorem r_reference89_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 0)=true := by decide +kernel
theorem a_reference89_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 1)=true := by decide +kernel
theorem rank_r_link89_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r89 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link89_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0011.a89.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a89 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints89 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell true ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r89 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile89_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link89_checked
    geometry89_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell false ReferenceProfileData.CoarseLowerShape.Batch0011.a89.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a89 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile89_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link89_checked
    geometry89_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks89_linked.1,←ranks89_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0011.r89.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a89.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0011.ordered89_checked hr ha ho
theorem frozen_frame89 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89 ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds ReferenceProfileData.CoarseLowerShape.Batch0011.a89.bounds
  · rw [←r_profile89_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile89_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry89_linked.2.2.2.2.1
  · exact geometry89_linked.2.2.2.2.2
  · exact r_reference89_checked
  · exact a_reference89_checked
  · exact r_fixed89_linked
  · exact a_fixed89_linked
  · exact time89_checked
  · exact ht
  · exact hw
theorem child_geometry89_checked : ReferenceWeightData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights89 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0022.cert178∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch22_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0022.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0022.cert179∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch22_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0022.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry89_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights178_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry89_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry89_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights179_linked j (List.mem_finRange j))
theorem actual_frozen_frame89 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame89 (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.flow.timeParameter_mem child_geometry89_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights89 hz)
theorem r_profile90_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r90=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds := by rfl
theorem a_profile90_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a90=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a90.bounds := by rfl
theorem r_fixed90_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 7 := by decide +kernel
theorem a_fixed90_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a90.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.a90.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 9 := by decide +kernel
theorem ranks90_linked : ReferenceRankData.CoarseLowerShape.Batch0011.targetR90=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0011.targetA90=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 1 := by decide +kernel
theorem r_input90_linked : ReferenceRankData.CoarseLowerShape.Batch0011.r90.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds.gauge] := by decide +kernel
theorem a_input90_linked : ReferenceRankData.CoarseLowerShape.Batch0011.a90.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.a90.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.a90.bounds.gauge] := by decide +kernel
theorem geometry90_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.a := by decide +kernel
theorem weights180_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0022.cert180.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights181_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0022.cert181.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time90_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 10)=true := by decide +kernel
theorem r_reference90_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 0)=true := by decide +kernel
theorem a_reference90_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 1)=true := by decide +kernel
theorem rank_r_link90_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r90 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link90_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0011.a90.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a90 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints90 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell true ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r90 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile90_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link90_checked
    geometry90_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell false ReferenceProfileData.CoarseLowerShape.Batch0011.a90.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a90 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile90_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link90_checked
    geometry90_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks90_linked.1,←ranks90_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0011.r90.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a90.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0011.ordered90_checked hr ha ho
theorem frozen_frame90 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90 ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds ReferenceProfileData.CoarseLowerShape.Batch0011.a90.bounds
  · rw [←r_profile90_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile90_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry90_linked.2.2.2.2.1
  · exact geometry90_linked.2.2.2.2.2
  · exact r_reference90_checked
  · exact a_reference90_checked
  · exact r_fixed90_linked
  · exact a_fixed90_linked
  · exact time90_checked
  · exact ht
  · exact hw
theorem child_geometry90_checked : ReferenceWeightData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights90 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0022.cert180∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch22_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0022.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0022.cert181∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch22_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0022.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry90_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights180_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry90_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry90_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights181_linked j (List.mem_finRange j))
theorem actual_frozen_frame90 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame90 (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.flow.timeParameter_mem child_geometry90_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights90 hz)
theorem r_profile91_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r91=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds := by rfl
theorem a_profile91_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a91=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a91.bounds := by rfl
theorem r_fixed91_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 7 := by decide +kernel
theorem a_fixed91_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a91.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.a91.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 9 := by decide +kernel
theorem ranks91_linked : ReferenceRankData.CoarseLowerShape.Batch0011.targetR91=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0011.targetA91=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 1 := by decide +kernel
theorem r_input91_linked : ReferenceRankData.CoarseLowerShape.Batch0011.r91.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds.gauge] := by decide +kernel
theorem a_input91_linked : ReferenceRankData.CoarseLowerShape.Batch0011.a91.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.a91.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.a91.bounds.gauge] := by decide +kernel
theorem geometry91_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.a := by decide +kernel
theorem weights182_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0022.cert182.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights183_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0022.cert183.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time91_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 10)=true := by decide +kernel
theorem r_reference91_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 0)=true := by decide +kernel
theorem a_reference91_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 1)=true := by decide +kernel
theorem rank_r_link91_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r91 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link91_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0011.a91.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a91 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints91 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell true ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r91 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile91_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link91_checked
    geometry91_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell false ReferenceProfileData.CoarseLowerShape.Batch0011.a91.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a91 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile91_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link91_checked
    geometry91_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks91_linked.1,←ranks91_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0011.r91.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a91.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0011.ordered91_checked hr ha ho
theorem frozen_frame91 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91 ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds ReferenceProfileData.CoarseLowerShape.Batch0011.a91.bounds
  · rw [←r_profile91_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile91_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry91_linked.2.2.2.2.1
  · exact geometry91_linked.2.2.2.2.2
  · exact r_reference91_checked
  · exact a_reference91_checked
  · exact r_fixed91_linked
  · exact a_fixed91_linked
  · exact time91_checked
  · exact ht
  · exact hw
theorem child_geometry91_checked : ReferenceWeightData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights91 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0022.cert182∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch22_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0022.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0022.cert183∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch22_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0022.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry91_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights182_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry91_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry91_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights183_linked j (List.mem_finRange j))
theorem actual_frozen_frame91 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame91 (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.flow.timeParameter_mem child_geometry91_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights91 hz)
theorem r_profile92_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r92=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds := by rfl
theorem a_profile92_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a92=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a92.bounds := by rfl
theorem r_fixed92_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 7 := by decide +kernel
theorem a_fixed92_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a92.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.a92.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 9 := by decide +kernel
theorem ranks92_linked : ReferenceRankData.CoarseLowerShape.Batch0011.targetR92=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0011.targetA92=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 1 := by decide +kernel
theorem r_input92_linked : ReferenceRankData.CoarseLowerShape.Batch0011.r92.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds.gauge] := by decide +kernel
theorem a_input92_linked : ReferenceRankData.CoarseLowerShape.Batch0011.a92.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.a92.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.a92.bounds.gauge] := by decide +kernel
theorem geometry92_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.a := by decide +kernel
theorem weights184_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0023.cert184.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights185_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0023.cert185.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time92_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 10)=true := by decide +kernel
theorem r_reference92_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 0)=true := by decide +kernel
theorem a_reference92_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 1)=true := by decide +kernel
theorem rank_r_link92_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r92 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link92_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0011.a92.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a92 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints92 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell true ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r92 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile92_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link92_checked
    geometry92_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell false ReferenceProfileData.CoarseLowerShape.Batch0011.a92.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a92 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile92_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link92_checked
    geometry92_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks92_linked.1,←ranks92_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0011.r92.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a92.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0011.ordered92_checked hr ha ho
theorem frozen_frame92 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92 ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds ReferenceProfileData.CoarseLowerShape.Batch0011.a92.bounds
  · rw [←r_profile92_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile92_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry92_linked.2.2.2.2.1
  · exact geometry92_linked.2.2.2.2.2
  · exact r_reference92_checked
  · exact a_reference92_checked
  · exact r_fixed92_linked
  · exact a_fixed92_linked
  · exact time92_checked
  · exact ht
  · exact hw
theorem child_geometry92_checked : ReferenceWeightData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights92 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0023.cert184∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch23_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0023.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0023.cert185∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch23_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0023.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry92_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights184_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry92_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry92_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights185_linked j (List.mem_finRange j))
theorem actual_frozen_frame92 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame92 (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.flow.timeParameter_mem child_geometry92_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights92 hz)
theorem r_profile93_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r93=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds := by rfl
theorem a_profile93_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a93=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a93.bounds := by rfl
theorem r_fixed93_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 7 := by decide +kernel
theorem a_fixed93_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a93.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.a93.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 9 := by decide +kernel
theorem ranks93_linked : ReferenceRankData.CoarseLowerShape.Batch0011.targetR93=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0011.targetA93=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 1 := by decide +kernel
theorem r_input93_linked : ReferenceRankData.CoarseLowerShape.Batch0011.r93.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds.gauge] := by decide +kernel
theorem a_input93_linked : ReferenceRankData.CoarseLowerShape.Batch0011.a93.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.a93.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.a93.bounds.gauge] := by decide +kernel
theorem geometry93_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.a := by decide +kernel
theorem weights186_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0023.cert186.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights187_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0023.cert187.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time93_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 10)=true := by decide +kernel
theorem r_reference93_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 0)=true := by decide +kernel
theorem a_reference93_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 1)=true := by decide +kernel
theorem rank_r_link93_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r93 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link93_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0011.a93.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a93 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints93 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell true ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r93 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile93_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link93_checked
    geometry93_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell false ReferenceProfileData.CoarseLowerShape.Batch0011.a93.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a93 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile93_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link93_checked
    geometry93_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks93_linked.1,←ranks93_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0011.r93.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a93.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0011.ordered93_checked hr ha ho
theorem frozen_frame93 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93 ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds ReferenceProfileData.CoarseLowerShape.Batch0011.a93.bounds
  · rw [←r_profile93_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile93_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry93_linked.2.2.2.2.1
  · exact geometry93_linked.2.2.2.2.2
  · exact r_reference93_checked
  · exact a_reference93_checked
  · exact r_fixed93_linked
  · exact a_fixed93_linked
  · exact time93_checked
  · exact ht
  · exact hw
theorem child_geometry93_checked : ReferenceWeightData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights93 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0023.cert186∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch23_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0023.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0023.cert187∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch23_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0023.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry93_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights186_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry93_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry93_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights187_linked j (List.mem_finRange j))
theorem actual_frozen_frame93 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame93 (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.flow.timeParameter_mem child_geometry93_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights93 hz)
theorem r_profile94_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r94=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds := by rfl
theorem a_profile94_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a94=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a94.bounds := by rfl
theorem r_fixed94_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 7 := by decide +kernel
theorem a_fixed94_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a94.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.a94.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 9 := by decide +kernel
theorem ranks94_linked : ReferenceRankData.CoarseLowerShape.Batch0011.targetR94=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0011.targetA94=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 1 := by decide +kernel
theorem r_input94_linked : ReferenceRankData.CoarseLowerShape.Batch0011.r94.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds.gauge] := by decide +kernel
theorem a_input94_linked : ReferenceRankData.CoarseLowerShape.Batch0011.a94.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.a94.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.a94.bounds.gauge] := by decide +kernel
theorem geometry94_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.a := by decide +kernel
theorem weights188_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0023.cert188.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights189_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0023.cert189.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time94_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 10)=true := by decide +kernel
theorem r_reference94_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 0)=true := by decide +kernel
theorem a_reference94_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 1)=true := by decide +kernel
theorem rank_r_link94_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r94 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link94_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0011.a94.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a94 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints94 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell true ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r94 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile94_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link94_checked
    geometry94_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell false ReferenceProfileData.CoarseLowerShape.Batch0011.a94.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a94 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile94_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link94_checked
    geometry94_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks94_linked.1,←ranks94_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0011.r94.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a94.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0011.ordered94_checked hr ha ho
theorem frozen_frame94 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94 ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds ReferenceProfileData.CoarseLowerShape.Batch0011.a94.bounds
  · rw [←r_profile94_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile94_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry94_linked.2.2.2.2.1
  · exact geometry94_linked.2.2.2.2.2
  · exact r_reference94_checked
  · exact a_reference94_checked
  · exact r_fixed94_linked
  · exact a_fixed94_linked
  · exact time94_checked
  · exact ht
  · exact hw
theorem child_geometry94_checked : ReferenceWeightData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights94 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0023.cert188∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch23_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0023.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0023.cert189∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch23_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0023.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry94_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights188_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry94_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry94_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights189_linked j (List.mem_finRange j))
theorem actual_frozen_frame94 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame94 (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.flow.timeParameter_mem child_geometry94_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights94 hz)
theorem r_profile95_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r95=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds := by rfl
theorem a_profile95_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a95=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a95.bounds := by rfl
theorem r_fixed95_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 7 := by decide +kernel
theorem a_fixed95_linked : ReferenceProfileData.CoarseLowerShape.Batch0011.a95.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0011.a95.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 9 := by decide +kernel
theorem ranks95_linked : ReferenceRankData.CoarseLowerShape.Batch0011.targetR95=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0011.targetA95=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 1 := by decide +kernel
theorem r_input95_linked : ReferenceRankData.CoarseLowerShape.Batch0011.r95.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds.gauge] := by decide +kernel
theorem a_input95_linked : ReferenceRankData.CoarseLowerShape.Batch0011.a95.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0011.a95.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0011.a95.bounds.gauge] := by decide +kernel
theorem geometry95_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.a := by decide +kernel
theorem weights190_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0023.cert190.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights191_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0023.cert191.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time95_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 10)=true := by decide +kernel
theorem r_reference95_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 0)=true := by decide +kernel
theorem a_reference95_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 1)=true := by decide +kernel
theorem rank_r_link95_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r95 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link95_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0011.a95.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a95 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints95 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell true ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds ReferenceRankData.CoarseLowerShape.Batch0011.r95 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile95_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link95_checked
    geometry95_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell false ReferenceProfileData.CoarseLowerShape.Batch0011.a95.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a95 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile95_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0011.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0011.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link95_checked
    geometry95_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks95_linked.1,←ranks95_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0011.r95.bounds ReferenceRankData.CoarseLowerShape.Batch0011.a95.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0011.ordered95_checked hr ha ho
theorem frozen_frame95 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95 ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds ReferenceProfileData.CoarseLowerShape.Batch0011.a95.bounds
  · rw [←r_profile95_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile95_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry95_linked.2.2.2.2.1
  · exact geometry95_linked.2.2.2.2.2
  · exact r_reference95_checked
  · exact a_reference95_checked
  · exact r_fixed95_linked
  · exact a_fixed95_linked
  · exact time95_checked
  · exact ht
  · exact hw
theorem child_geometry95_checked : ReferenceWeightData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights95 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0023.cert190∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch23_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0023.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0023.cert191∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch23_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0023.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry95_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights190_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry95_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry95_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights191_linked j (List.mem_finRange j))
theorem actual_frozen_frame95 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame95 (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.flow.timeParameter_mem child_geometry95_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights95 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell88),(ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell89),(ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell90),(ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell91),(ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell92),(ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell93),(ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell94),(ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0011.cell95)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0011.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0011.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame88 hz
  · exact fun z hz=>actual_frozen_frame89 hz
  · exact fun z hz=>actual_frozen_frame90 hz
  · exact fun z hz=>actual_frozen_frame91 hz
  · exact fun z hz=>actual_frozen_frame92 hz
  · exact fun z hz=>actual_frozen_frame93 hz
  · exact fun z hz=>actual_frozen_frame94 hz
  · exact fun z hz=>actual_frozen_frame95 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints88 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints89 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints90 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints91 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints92 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints93 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints94 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints95 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry88_linked.1,geometry88_linked.2.1,geometry88_linked.2.2.1,geometry88_linked.2.2.2.1⟩
  · exact ⟨geometry89_linked.1,geometry89_linked.2.1,geometry89_linked.2.2.1,geometry89_linked.2.2.2.1⟩
  · exact ⟨geometry90_linked.1,geometry90_linked.2.1,geometry90_linked.2.2.1,geometry90_linked.2.2.2.1⟩
  · exact ⟨geometry91_linked.1,geometry91_linked.2.1,geometry91_linked.2.2.1,geometry91_linked.2.2.2.1⟩
  · exact ⟨geometry92_linked.1,geometry92_linked.2.1,geometry92_linked.2.2.1,geometry92_linked.2.2.2.1⟩
  · exact ⟨geometry93_linked.1,geometry93_linked.2.1,geometry93_linked.2.2.1,geometry93_linked.2.2.2.1⟩
  · exact ⟨geometry94_linked.1,geometry94_linked.2.1,geometry94_linked.2.2.1,geometry94_linked.2.2.2.1⟩
  · exact ⟨geometry95_linked.1,geometry95_linked.2.1,geometry95_linked.2.2.1,geometry95_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.a88.bounds,?_,geometry88_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a88.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile88_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds,?_,geometry88_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert88.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r88.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile88_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.a89.bounds,?_,geometry89_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a89.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile89_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds,?_,geometry89_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert89.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r89.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile89_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.a90.bounds,?_,geometry90_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a90.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile90_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds,?_,geometry90_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert90.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r90.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile90_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.a91.bounds,?_,geometry91_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a91.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile91_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds,?_,geometry91_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert91.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r91.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile91_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.a92.bounds,?_,geometry92_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a92.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile92_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds,?_,geometry92_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert92.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r92.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile92_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.a93.bounds,?_,geometry93_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a93.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile93_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds,?_,geometry93_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert93.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r93.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile93_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.a94.bounds,?_,geometry94_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a94.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile94_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds,?_,geometry94_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert94.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r94.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile94_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.a95.bounds,?_,geometry95_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0011.a95.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile95_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds,?_,geometry95_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0011.cert95.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0011.r95.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile95_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0011.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0011.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0011
