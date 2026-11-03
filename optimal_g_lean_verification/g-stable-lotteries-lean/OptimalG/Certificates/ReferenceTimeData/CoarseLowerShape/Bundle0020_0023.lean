import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0017_0020
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0017_0020
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0041_0044
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0018_0021
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0019_0022
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Bundle0016_0019
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0021_0024
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0021_0024
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0045_0048
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0022_0025
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0023_0026

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0020
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch40_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0040.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0040.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch41_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0041.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0041.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile160_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r160=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds := by rfl
theorem a_profile160_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a160=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a160.bounds := by rfl
theorem r_fixed160_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 7 := by decide +kernel
theorem a_fixed160_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a160.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.a160.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 9 := by decide +kernel
theorem ranks160_linked : ReferenceRankData.CoarseLowerShape.Batch0020.targetR160=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0020.targetA160=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 1 := by decide +kernel
theorem r_input160_linked : ReferenceRankData.CoarseLowerShape.Batch0020.r160.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds.gauge] := by decide +kernel
theorem a_input160_linked : ReferenceRankData.CoarseLowerShape.Batch0020.a160.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.a160.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.a160.bounds.gauge] := by decide +kernel
theorem geometry160_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.a := by decide +kernel
theorem weights320_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0040.cert320.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights321_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0040.cert321.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time160_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 10)=true := by decide +kernel
theorem r_reference160_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 0)=true := by decide +kernel
theorem a_reference160_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 1)=true := by decide +kernel
theorem rank_r_link160_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r160 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link160_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0020.a160.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a160 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints160 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell true ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r160 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile160_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link160_checked
    geometry160_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell false ReferenceProfileData.CoarseLowerShape.Batch0020.a160.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a160 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile160_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link160_checked
    geometry160_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks160_linked.1,←ranks160_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0020.r160.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a160.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0020.ordered160_checked hr ha ho
theorem frozen_frame160 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160 ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds ReferenceProfileData.CoarseLowerShape.Batch0020.a160.bounds
  · rw [←r_profile160_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile160_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry160_linked.2.2.2.2.1
  · exact geometry160_linked.2.2.2.2.2
  · exact r_reference160_checked
  · exact a_reference160_checked
  · exact r_fixed160_linked
  · exact a_fixed160_linked
  · exact time160_checked
  · exact ht
  · exact hw
theorem child_geometry160_checked : ReferenceWeightData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights160 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0040.cert320∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch40_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0040.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0040.cert321∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch40_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0040.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0040.cert320.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry160_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights320_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0040.cert321.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry160_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry160_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights321_linked j (List.mem_finRange j))
theorem actual_frozen_frame160 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame160 (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.flow.timeParameter_mem child_geometry160_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights160 hz)
theorem r_profile161_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r161=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds := by rfl
theorem a_profile161_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a161=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a161.bounds := by rfl
theorem r_fixed161_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 7 := by decide +kernel
theorem a_fixed161_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a161.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.a161.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 9 := by decide +kernel
theorem ranks161_linked : ReferenceRankData.CoarseLowerShape.Batch0020.targetR161=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0020.targetA161=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 1 := by decide +kernel
theorem r_input161_linked : ReferenceRankData.CoarseLowerShape.Batch0020.r161.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds.gauge] := by decide +kernel
theorem a_input161_linked : ReferenceRankData.CoarseLowerShape.Batch0020.a161.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.a161.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.a161.bounds.gauge] := by decide +kernel
theorem geometry161_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.a := by decide +kernel
theorem weights322_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0040.cert322.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights323_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0040.cert323.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time161_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 10)=true := by decide +kernel
theorem r_reference161_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 0)=true := by decide +kernel
theorem a_reference161_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 1)=true := by decide +kernel
theorem rank_r_link161_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r161 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link161_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0020.a161.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a161 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints161 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell true ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r161 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile161_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link161_checked
    geometry161_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell false ReferenceProfileData.CoarseLowerShape.Batch0020.a161.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a161 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile161_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link161_checked
    geometry161_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks161_linked.1,←ranks161_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0020.r161.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a161.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0020.ordered161_checked hr ha ho
theorem frozen_frame161 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161 ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds ReferenceProfileData.CoarseLowerShape.Batch0020.a161.bounds
  · rw [←r_profile161_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile161_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry161_linked.2.2.2.2.1
  · exact geometry161_linked.2.2.2.2.2
  · exact r_reference161_checked
  · exact a_reference161_checked
  · exact r_fixed161_linked
  · exact a_fixed161_linked
  · exact time161_checked
  · exact ht
  · exact hw
theorem child_geometry161_checked : ReferenceWeightData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights161 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0040.cert322∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch40_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0040.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0040.cert323∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch40_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0040.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0040.cert322.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry161_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights322_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0040.cert323.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry161_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry161_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights323_linked j (List.mem_finRange j))
theorem actual_frozen_frame161 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame161 (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.flow.timeParameter_mem child_geometry161_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights161 hz)
theorem r_profile162_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r162=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds := by rfl
theorem a_profile162_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a162=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a162.bounds := by rfl
theorem r_fixed162_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 7 := by decide +kernel
theorem a_fixed162_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a162.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.a162.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 9 := by decide +kernel
theorem ranks162_linked : ReferenceRankData.CoarseLowerShape.Batch0020.targetR162=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0020.targetA162=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 1 := by decide +kernel
theorem r_input162_linked : ReferenceRankData.CoarseLowerShape.Batch0020.r162.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds.gauge] := by decide +kernel
theorem a_input162_linked : ReferenceRankData.CoarseLowerShape.Batch0020.a162.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.a162.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.a162.bounds.gauge] := by decide +kernel
theorem geometry162_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.a := by decide +kernel
theorem weights324_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0040.cert324.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights325_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0040.cert325.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time162_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 10)=true := by decide +kernel
theorem r_reference162_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 0)=true := by decide +kernel
theorem a_reference162_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 1)=true := by decide +kernel
theorem rank_r_link162_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r162 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link162_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0020.a162.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a162 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints162 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell true ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r162 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile162_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link162_checked
    geometry162_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell false ReferenceProfileData.CoarseLowerShape.Batch0020.a162.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a162 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile162_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link162_checked
    geometry162_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks162_linked.1,←ranks162_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0020.r162.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a162.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0020.ordered162_checked hr ha ho
theorem frozen_frame162 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162 ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds ReferenceProfileData.CoarseLowerShape.Batch0020.a162.bounds
  · rw [←r_profile162_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile162_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry162_linked.2.2.2.2.1
  · exact geometry162_linked.2.2.2.2.2
  · exact r_reference162_checked
  · exact a_reference162_checked
  · exact r_fixed162_linked
  · exact a_fixed162_linked
  · exact time162_checked
  · exact ht
  · exact hw
theorem child_geometry162_checked : ReferenceWeightData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights162 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0040.cert324∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch40_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0040.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0040.cert325∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch40_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0040.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0040.cert324.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry162_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights324_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0040.cert325.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry162_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry162_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights325_linked j (List.mem_finRange j))
theorem actual_frozen_frame162 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame162 (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.flow.timeParameter_mem child_geometry162_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights162 hz)
theorem r_profile163_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r163=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds := by rfl
theorem a_profile163_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a163=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a163.bounds := by rfl
theorem r_fixed163_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 7 := by decide +kernel
theorem a_fixed163_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a163.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.a163.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 9 := by decide +kernel
theorem ranks163_linked : ReferenceRankData.CoarseLowerShape.Batch0020.targetR163=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0020.targetA163=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 1 := by decide +kernel
theorem r_input163_linked : ReferenceRankData.CoarseLowerShape.Batch0020.r163.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds.gauge] := by decide +kernel
theorem a_input163_linked : ReferenceRankData.CoarseLowerShape.Batch0020.a163.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.a163.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.a163.bounds.gauge] := by decide +kernel
theorem geometry163_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.a := by decide +kernel
theorem weights326_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0040.cert326.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights327_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0040.cert327.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time163_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 10)=true := by decide +kernel
theorem r_reference163_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 0)=true := by decide +kernel
theorem a_reference163_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 1)=true := by decide +kernel
theorem rank_r_link163_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r163 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link163_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0020.a163.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a163 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints163 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell true ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r163 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile163_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link163_checked
    geometry163_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell false ReferenceProfileData.CoarseLowerShape.Batch0020.a163.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a163 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile163_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link163_checked
    geometry163_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks163_linked.1,←ranks163_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0020.r163.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a163.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0020.ordered163_checked hr ha ho
theorem frozen_frame163 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163 ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds ReferenceProfileData.CoarseLowerShape.Batch0020.a163.bounds
  · rw [←r_profile163_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile163_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry163_linked.2.2.2.2.1
  · exact geometry163_linked.2.2.2.2.2
  · exact r_reference163_checked
  · exact a_reference163_checked
  · exact r_fixed163_linked
  · exact a_fixed163_linked
  · exact time163_checked
  · exact ht
  · exact hw
theorem child_geometry163_checked : ReferenceWeightData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights163 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0040.cert326∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch40_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0040.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0040.cert327∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch40_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0040.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0040.cert326.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry163_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights326_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0040.cert327.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry163_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry163_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights327_linked j (List.mem_finRange j))
theorem actual_frozen_frame163 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame163 (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.flow.timeParameter_mem child_geometry163_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights163 hz)
theorem r_profile164_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r164=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds := by rfl
theorem a_profile164_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a164=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a164.bounds := by rfl
theorem r_fixed164_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 7 := by decide +kernel
theorem a_fixed164_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a164.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.a164.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 9 := by decide +kernel
theorem ranks164_linked : ReferenceRankData.CoarseLowerShape.Batch0020.targetR164=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0020.targetA164=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 1 := by decide +kernel
theorem r_input164_linked : ReferenceRankData.CoarseLowerShape.Batch0020.r164.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds.gauge] := by decide +kernel
theorem a_input164_linked : ReferenceRankData.CoarseLowerShape.Batch0020.a164.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.a164.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.a164.bounds.gauge] := by decide +kernel
theorem geometry164_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.a := by decide +kernel
theorem weights328_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0041.cert328.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights329_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0041.cert329.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time164_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 10)=true := by decide +kernel
theorem r_reference164_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 0)=true := by decide +kernel
theorem a_reference164_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 1)=true := by decide +kernel
theorem rank_r_link164_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r164 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link164_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0020.a164.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a164 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints164 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell true ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r164 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile164_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link164_checked
    geometry164_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell false ReferenceProfileData.CoarseLowerShape.Batch0020.a164.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a164 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile164_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link164_checked
    geometry164_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks164_linked.1,←ranks164_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0020.r164.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a164.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0020.ordered164_checked hr ha ho
theorem frozen_frame164 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164 ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds ReferenceProfileData.CoarseLowerShape.Batch0020.a164.bounds
  · rw [←r_profile164_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile164_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry164_linked.2.2.2.2.1
  · exact geometry164_linked.2.2.2.2.2
  · exact r_reference164_checked
  · exact a_reference164_checked
  · exact r_fixed164_linked
  · exact a_fixed164_linked
  · exact time164_checked
  · exact ht
  · exact hw
theorem child_geometry164_checked : ReferenceWeightData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights164 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0041.cert328∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch41_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0041.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0041.cert329∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch41_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0041.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0041.cert328.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry164_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights328_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0041.cert329.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry164_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry164_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights329_linked j (List.mem_finRange j))
theorem actual_frozen_frame164 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame164 (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.flow.timeParameter_mem child_geometry164_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights164 hz)
theorem r_profile165_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r165=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds := by rfl
theorem a_profile165_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a165=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a165.bounds := by rfl
theorem r_fixed165_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 7 := by decide +kernel
theorem a_fixed165_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a165.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.a165.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 9 := by decide +kernel
theorem ranks165_linked : ReferenceRankData.CoarseLowerShape.Batch0020.targetR165=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0020.targetA165=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 1 := by decide +kernel
theorem r_input165_linked : ReferenceRankData.CoarseLowerShape.Batch0020.r165.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds.gauge] := by decide +kernel
theorem a_input165_linked : ReferenceRankData.CoarseLowerShape.Batch0020.a165.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.a165.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.a165.bounds.gauge] := by decide +kernel
theorem geometry165_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.a := by decide +kernel
theorem weights330_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0041.cert330.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights331_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0041.cert331.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time165_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 10)=true := by decide +kernel
theorem r_reference165_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 0)=true := by decide +kernel
theorem a_reference165_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 1)=true := by decide +kernel
theorem rank_r_link165_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r165 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link165_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0020.a165.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a165 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints165 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell true ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r165 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile165_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link165_checked
    geometry165_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell false ReferenceProfileData.CoarseLowerShape.Batch0020.a165.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a165 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile165_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link165_checked
    geometry165_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks165_linked.1,←ranks165_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0020.r165.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a165.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0020.ordered165_checked hr ha ho
theorem frozen_frame165 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165 ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds ReferenceProfileData.CoarseLowerShape.Batch0020.a165.bounds
  · rw [←r_profile165_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile165_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry165_linked.2.2.2.2.1
  · exact geometry165_linked.2.2.2.2.2
  · exact r_reference165_checked
  · exact a_reference165_checked
  · exact r_fixed165_linked
  · exact a_fixed165_linked
  · exact time165_checked
  · exact ht
  · exact hw
theorem child_geometry165_checked : ReferenceWeightData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights165 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0041.cert330∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch41_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0041.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0041.cert331∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch41_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0041.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0041.cert330.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry165_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights330_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0041.cert331.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry165_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry165_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights331_linked j (List.mem_finRange j))
theorem actual_frozen_frame165 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame165 (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.flow.timeParameter_mem child_geometry165_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights165 hz)
theorem r_profile166_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r166=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds := by rfl
theorem a_profile166_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a166=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a166.bounds := by rfl
theorem r_fixed166_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 7 := by decide +kernel
theorem a_fixed166_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a166.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.a166.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 9 := by decide +kernel
theorem ranks166_linked : ReferenceRankData.CoarseLowerShape.Batch0020.targetR166=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0020.targetA166=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 1 := by decide +kernel
theorem r_input166_linked : ReferenceRankData.CoarseLowerShape.Batch0020.r166.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds.gauge] := by decide +kernel
theorem a_input166_linked : ReferenceRankData.CoarseLowerShape.Batch0020.a166.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.a166.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.a166.bounds.gauge] := by decide +kernel
theorem geometry166_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.a := by decide +kernel
theorem weights332_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0041.cert332.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights333_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0041.cert333.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time166_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 10)=true := by decide +kernel
theorem r_reference166_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 0)=true := by decide +kernel
theorem a_reference166_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 1)=true := by decide +kernel
theorem rank_r_link166_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r166 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link166_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0020.a166.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a166 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints166 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell true ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r166 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile166_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link166_checked
    geometry166_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell false ReferenceProfileData.CoarseLowerShape.Batch0020.a166.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a166 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile166_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link166_checked
    geometry166_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks166_linked.1,←ranks166_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0020.r166.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a166.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0020.ordered166_checked hr ha ho
theorem frozen_frame166 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166 ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds ReferenceProfileData.CoarseLowerShape.Batch0020.a166.bounds
  · rw [←r_profile166_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile166_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry166_linked.2.2.2.2.1
  · exact geometry166_linked.2.2.2.2.2
  · exact r_reference166_checked
  · exact a_reference166_checked
  · exact r_fixed166_linked
  · exact a_fixed166_linked
  · exact time166_checked
  · exact ht
  · exact hw
theorem child_geometry166_checked : ReferenceWeightData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights166 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0041.cert332∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch41_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0041.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0041.cert333∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch41_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0041.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0041.cert332.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry166_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights332_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0041.cert333.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry166_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry166_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights333_linked j (List.mem_finRange j))
theorem actual_frozen_frame166 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame166 (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.flow.timeParameter_mem child_geometry166_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights166 hz)
theorem r_profile167_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r167=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds := by rfl
theorem a_profile167_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a167=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a167.bounds := by rfl
theorem r_fixed167_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 7 := by decide +kernel
theorem a_fixed167_linked : ReferenceProfileData.CoarseLowerShape.Batch0020.a167.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0020.a167.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 9 := by decide +kernel
theorem ranks167_linked : ReferenceRankData.CoarseLowerShape.Batch0020.targetR167=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0020.targetA167=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 1 := by decide +kernel
theorem r_input167_linked : ReferenceRankData.CoarseLowerShape.Batch0020.r167.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds.gauge] := by decide +kernel
theorem a_input167_linked : ReferenceRankData.CoarseLowerShape.Batch0020.a167.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0020.a167.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0020.a167.bounds.gauge] := by decide +kernel
theorem geometry167_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.a := by decide +kernel
theorem weights334_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0041.cert334.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights335_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0041.cert335.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time167_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 10)=true := by decide +kernel
theorem r_reference167_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 0)=true := by decide +kernel
theorem a_reference167_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 1)=true := by decide +kernel
theorem rank_r_link167_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r167 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link167_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0020.a167.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a167 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints167 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell true ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds ReferenceRankData.CoarseLowerShape.Batch0020.r167 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile167_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link167_checked
    geometry167_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell false ReferenceProfileData.CoarseLowerShape.Batch0020.a167.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a167 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile167_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0020.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0020.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link167_checked
    geometry167_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks167_linked.1,←ranks167_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0020.r167.bounds ReferenceRankData.CoarseLowerShape.Batch0020.a167.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0020.ordered167_checked hr ha ho
theorem frozen_frame167 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167 ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds ReferenceProfileData.CoarseLowerShape.Batch0020.a167.bounds
  · rw [←r_profile167_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile167_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry167_linked.2.2.2.2.1
  · exact geometry167_linked.2.2.2.2.2
  · exact r_reference167_checked
  · exact a_reference167_checked
  · exact r_fixed167_linked
  · exact a_fixed167_linked
  · exact time167_checked
  · exact ht
  · exact hw
theorem child_geometry167_checked : ReferenceWeightData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights167 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0041.cert334∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch41_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0041.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0041.cert335∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch41_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0041.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0041.cert334.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry167_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights334_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0041.cert335.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry167_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry167_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights335_linked j (List.mem_finRange j))
theorem actual_frozen_frame167 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame167 (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.flow.timeParameter_mem child_geometry167_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights167 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell160),(ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell161),(ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell162),(ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell163),(ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell164),(ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell165),(ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell166),(ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0020.cell167)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0020.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0020.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame160 hz
  · exact fun z hz=>actual_frozen_frame161 hz
  · exact fun z hz=>actual_frozen_frame162 hz
  · exact fun z hz=>actual_frozen_frame163 hz
  · exact fun z hz=>actual_frozen_frame164 hz
  · exact fun z hz=>actual_frozen_frame165 hz
  · exact fun z hz=>actual_frozen_frame166 hz
  · exact fun z hz=>actual_frozen_frame167 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints160 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints161 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints162 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints163 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints164 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints165 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints166 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints167 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry160_linked.1,geometry160_linked.2.1,geometry160_linked.2.2.1,geometry160_linked.2.2.2.1⟩
  · exact ⟨geometry161_linked.1,geometry161_linked.2.1,geometry161_linked.2.2.1,geometry161_linked.2.2.2.1⟩
  · exact ⟨geometry162_linked.1,geometry162_linked.2.1,geometry162_linked.2.2.1,geometry162_linked.2.2.2.1⟩
  · exact ⟨geometry163_linked.1,geometry163_linked.2.1,geometry163_linked.2.2.1,geometry163_linked.2.2.2.1⟩
  · exact ⟨geometry164_linked.1,geometry164_linked.2.1,geometry164_linked.2.2.1,geometry164_linked.2.2.2.1⟩
  · exact ⟨geometry165_linked.1,geometry165_linked.2.1,geometry165_linked.2.2.1,geometry165_linked.2.2.2.1⟩
  · exact ⟨geometry166_linked.1,geometry166_linked.2.1,geometry166_linked.2.2.1,geometry166_linked.2.2.2.1⟩
  · exact ⟨geometry167_linked.1,geometry167_linked.2.1,geometry167_linked.2.2.1,geometry167_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.a160.bounds,?_,geometry160_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a160.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile160_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds,?_,geometry160_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert160.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r160.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile160_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.a161.bounds,?_,geometry161_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a161.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile161_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds,?_,geometry161_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert161.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r161.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile161_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.a162.bounds,?_,geometry162_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a162.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile162_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds,?_,geometry162_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert162.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r162.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile162_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.a163.bounds,?_,geometry163_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a163.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile163_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds,?_,geometry163_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert163.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r163.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile163_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.a164.bounds,?_,geometry164_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a164.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile164_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds,?_,geometry164_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert164.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r164.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile164_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.a165.bounds,?_,geometry165_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a165.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile165_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds,?_,geometry165_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert165.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r165.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile165_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.a166.bounds,?_,geometry166_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a166.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile166_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds,?_,geometry166_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert166.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r166.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile166_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.a167.bounds,?_,geometry167_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0020.a167.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile167_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds,?_,geometry167_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0020.cert167.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0020.r167.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile167_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0020.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0020.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0020

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0021
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch42_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0042.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0042.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch43_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0043.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0043.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile168_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r168=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds := by rfl
theorem a_profile168_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a168=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a168.bounds := by rfl
theorem r_fixed168_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 7 := by decide +kernel
theorem a_fixed168_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a168.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.a168.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 9 := by decide +kernel
theorem ranks168_linked : ReferenceRankData.CoarseLowerShape.Batch0021.targetR168=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0021.targetA168=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 1 := by decide +kernel
theorem r_input168_linked : ReferenceRankData.CoarseLowerShape.Batch0021.r168.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds.gauge] := by decide +kernel
theorem a_input168_linked : ReferenceRankData.CoarseLowerShape.Batch0021.a168.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.a168.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.a168.bounds.gauge] := by decide +kernel
theorem geometry168_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.a := by decide +kernel
theorem weights336_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0042.cert336.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights337_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0042.cert337.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time168_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 10)=true := by decide +kernel
theorem r_reference168_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 0)=true := by decide +kernel
theorem a_reference168_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 1)=true := by decide +kernel
theorem rank_r_link168_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r168 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link168_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0021.a168.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a168 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints168 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell true ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r168 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile168_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link168_checked
    geometry168_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell false ReferenceProfileData.CoarseLowerShape.Batch0021.a168.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a168 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile168_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link168_checked
    geometry168_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks168_linked.1,←ranks168_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0021.r168.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a168.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0021.ordered168_checked hr ha ho
theorem frozen_frame168 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168 ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds ReferenceProfileData.CoarseLowerShape.Batch0021.a168.bounds
  · rw [←r_profile168_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile168_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry168_linked.2.2.2.2.1
  · exact geometry168_linked.2.2.2.2.2
  · exact r_reference168_checked
  · exact a_reference168_checked
  · exact r_fixed168_linked
  · exact a_fixed168_linked
  · exact time168_checked
  · exact ht
  · exact hw
theorem child_geometry168_checked : ReferenceWeightData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights168 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0042.cert336∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch42_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0042.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0042.cert337∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch42_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0042.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0042.cert336.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry168_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights336_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0042.cert337.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry168_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry168_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights337_linked j (List.mem_finRange j))
theorem actual_frozen_frame168 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame168 (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.flow.timeParameter_mem child_geometry168_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights168 hz)
theorem r_profile169_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r169=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds := by rfl
theorem a_profile169_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a169=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a169.bounds := by rfl
theorem r_fixed169_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 7 := by decide +kernel
theorem a_fixed169_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a169.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.a169.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 9 := by decide +kernel
theorem ranks169_linked : ReferenceRankData.CoarseLowerShape.Batch0021.targetR169=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0021.targetA169=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 1 := by decide +kernel
theorem r_input169_linked : ReferenceRankData.CoarseLowerShape.Batch0021.r169.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds.gauge] := by decide +kernel
theorem a_input169_linked : ReferenceRankData.CoarseLowerShape.Batch0021.a169.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.a169.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.a169.bounds.gauge] := by decide +kernel
theorem geometry169_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.a := by decide +kernel
theorem weights338_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0042.cert338.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights339_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0042.cert339.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time169_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 10)=true := by decide +kernel
theorem r_reference169_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 0)=true := by decide +kernel
theorem a_reference169_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 1)=true := by decide +kernel
theorem rank_r_link169_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r169 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link169_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0021.a169.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a169 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints169 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell true ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r169 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile169_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link169_checked
    geometry169_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell false ReferenceProfileData.CoarseLowerShape.Batch0021.a169.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a169 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile169_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link169_checked
    geometry169_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks169_linked.1,←ranks169_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0021.r169.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a169.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0021.ordered169_checked hr ha ho
theorem frozen_frame169 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169 ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds ReferenceProfileData.CoarseLowerShape.Batch0021.a169.bounds
  · rw [←r_profile169_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile169_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry169_linked.2.2.2.2.1
  · exact geometry169_linked.2.2.2.2.2
  · exact r_reference169_checked
  · exact a_reference169_checked
  · exact r_fixed169_linked
  · exact a_fixed169_linked
  · exact time169_checked
  · exact ht
  · exact hw
theorem child_geometry169_checked : ReferenceWeightData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights169 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0042.cert338∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch42_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0042.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0042.cert339∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch42_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0042.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0042.cert338.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry169_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights338_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0042.cert339.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry169_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry169_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights339_linked j (List.mem_finRange j))
theorem actual_frozen_frame169 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame169 (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.flow.timeParameter_mem child_geometry169_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights169 hz)
theorem r_profile170_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r170=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds := by rfl
theorem a_profile170_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a170=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a170.bounds := by rfl
theorem r_fixed170_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 7 := by decide +kernel
theorem a_fixed170_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a170.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.a170.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 9 := by decide +kernel
theorem ranks170_linked : ReferenceRankData.CoarseLowerShape.Batch0021.targetR170=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0021.targetA170=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 1 := by decide +kernel
theorem r_input170_linked : ReferenceRankData.CoarseLowerShape.Batch0021.r170.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds.gauge] := by decide +kernel
theorem a_input170_linked : ReferenceRankData.CoarseLowerShape.Batch0021.a170.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.a170.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.a170.bounds.gauge] := by decide +kernel
theorem geometry170_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.a := by decide +kernel
theorem weights340_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0042.cert340.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights341_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0042.cert341.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time170_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 10)=true := by decide +kernel
theorem r_reference170_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 0)=true := by decide +kernel
theorem a_reference170_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 1)=true := by decide +kernel
theorem rank_r_link170_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r170 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link170_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0021.a170.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a170 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints170 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell true ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r170 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile170_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link170_checked
    geometry170_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell false ReferenceProfileData.CoarseLowerShape.Batch0021.a170.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a170 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile170_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link170_checked
    geometry170_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks170_linked.1,←ranks170_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0021.r170.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a170.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0021.ordered170_checked hr ha ho
theorem frozen_frame170 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170 ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds ReferenceProfileData.CoarseLowerShape.Batch0021.a170.bounds
  · rw [←r_profile170_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile170_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry170_linked.2.2.2.2.1
  · exact geometry170_linked.2.2.2.2.2
  · exact r_reference170_checked
  · exact a_reference170_checked
  · exact r_fixed170_linked
  · exact a_fixed170_linked
  · exact time170_checked
  · exact ht
  · exact hw
theorem child_geometry170_checked : ReferenceWeightData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights170 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0042.cert340∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch42_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0042.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0042.cert341∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch42_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0042.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0042.cert340.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry170_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights340_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0042.cert341.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry170_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry170_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights341_linked j (List.mem_finRange j))
theorem actual_frozen_frame170 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame170 (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.flow.timeParameter_mem child_geometry170_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights170 hz)
theorem r_profile171_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r171=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds := by rfl
theorem a_profile171_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a171=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a171.bounds := by rfl
theorem r_fixed171_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 7 := by decide +kernel
theorem a_fixed171_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a171.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.a171.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 9 := by decide +kernel
theorem ranks171_linked : ReferenceRankData.CoarseLowerShape.Batch0021.targetR171=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0021.targetA171=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 1 := by decide +kernel
theorem r_input171_linked : ReferenceRankData.CoarseLowerShape.Batch0021.r171.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds.gauge] := by decide +kernel
theorem a_input171_linked : ReferenceRankData.CoarseLowerShape.Batch0021.a171.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.a171.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.a171.bounds.gauge] := by decide +kernel
theorem geometry171_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.a := by decide +kernel
theorem weights342_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0042.cert342.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights343_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0042.cert343.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time171_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 10)=true := by decide +kernel
theorem r_reference171_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 0)=true := by decide +kernel
theorem a_reference171_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 1)=true := by decide +kernel
theorem rank_r_link171_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r171 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link171_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0021.a171.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a171 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints171 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell true ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r171 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile171_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link171_checked
    geometry171_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell false ReferenceProfileData.CoarseLowerShape.Batch0021.a171.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a171 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile171_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link171_checked
    geometry171_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks171_linked.1,←ranks171_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0021.r171.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a171.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0021.ordered171_checked hr ha ho
theorem frozen_frame171 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171 ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds ReferenceProfileData.CoarseLowerShape.Batch0021.a171.bounds
  · rw [←r_profile171_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile171_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry171_linked.2.2.2.2.1
  · exact geometry171_linked.2.2.2.2.2
  · exact r_reference171_checked
  · exact a_reference171_checked
  · exact r_fixed171_linked
  · exact a_fixed171_linked
  · exact time171_checked
  · exact ht
  · exact hw
theorem child_geometry171_checked : ReferenceWeightData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights171 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0042.cert342∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch42_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0042.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0042.cert343∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch42_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0042.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0042.cert342.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry171_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights342_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0042.cert343.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry171_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry171_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights343_linked j (List.mem_finRange j))
theorem actual_frozen_frame171 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame171 (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.flow.timeParameter_mem child_geometry171_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights171 hz)
theorem r_profile172_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r172=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds := by rfl
theorem a_profile172_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a172=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a172.bounds := by rfl
theorem r_fixed172_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 7 := by decide +kernel
theorem a_fixed172_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a172.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.a172.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 9 := by decide +kernel
theorem ranks172_linked : ReferenceRankData.CoarseLowerShape.Batch0021.targetR172=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0021.targetA172=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 1 := by decide +kernel
theorem r_input172_linked : ReferenceRankData.CoarseLowerShape.Batch0021.r172.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds.gauge] := by decide +kernel
theorem a_input172_linked : ReferenceRankData.CoarseLowerShape.Batch0021.a172.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.a172.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.a172.bounds.gauge] := by decide +kernel
theorem geometry172_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.a := by decide +kernel
theorem weights344_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0043.cert344.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights345_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0043.cert345.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time172_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 10)=true := by decide +kernel
theorem r_reference172_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 0)=true := by decide +kernel
theorem a_reference172_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 1)=true := by decide +kernel
theorem rank_r_link172_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r172 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link172_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0021.a172.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a172 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints172 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell true ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r172 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile172_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link172_checked
    geometry172_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell false ReferenceProfileData.CoarseLowerShape.Batch0021.a172.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a172 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile172_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link172_checked
    geometry172_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks172_linked.1,←ranks172_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0021.r172.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a172.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0021.ordered172_checked hr ha ho
theorem frozen_frame172 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172 ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds ReferenceProfileData.CoarseLowerShape.Batch0021.a172.bounds
  · rw [←r_profile172_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile172_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry172_linked.2.2.2.2.1
  · exact geometry172_linked.2.2.2.2.2
  · exact r_reference172_checked
  · exact a_reference172_checked
  · exact r_fixed172_linked
  · exact a_fixed172_linked
  · exact time172_checked
  · exact ht
  · exact hw
theorem child_geometry172_checked : ReferenceWeightData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights172 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0043.cert344∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch43_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0043.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0043.cert345∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch43_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0043.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0043.cert344.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry172_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights344_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0043.cert345.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry172_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry172_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights345_linked j (List.mem_finRange j))
theorem actual_frozen_frame172 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame172 (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.flow.timeParameter_mem child_geometry172_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights172 hz)
theorem r_profile173_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r173=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds := by rfl
theorem a_profile173_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a173=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a173.bounds := by rfl
theorem r_fixed173_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 7 := by decide +kernel
theorem a_fixed173_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a173.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.a173.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 9 := by decide +kernel
theorem ranks173_linked : ReferenceRankData.CoarseLowerShape.Batch0021.targetR173=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0021.targetA173=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 1 := by decide +kernel
theorem r_input173_linked : ReferenceRankData.CoarseLowerShape.Batch0021.r173.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds.gauge] := by decide +kernel
theorem a_input173_linked : ReferenceRankData.CoarseLowerShape.Batch0021.a173.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.a173.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.a173.bounds.gauge] := by decide +kernel
theorem geometry173_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.a := by decide +kernel
theorem weights346_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0043.cert346.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights347_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0043.cert347.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time173_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 10)=true := by decide +kernel
theorem r_reference173_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 0)=true := by decide +kernel
theorem a_reference173_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 1)=true := by decide +kernel
theorem rank_r_link173_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r173 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link173_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0021.a173.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a173 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints173 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell true ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r173 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile173_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link173_checked
    geometry173_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell false ReferenceProfileData.CoarseLowerShape.Batch0021.a173.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a173 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile173_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link173_checked
    geometry173_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks173_linked.1,←ranks173_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0021.r173.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a173.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0021.ordered173_checked hr ha ho
theorem frozen_frame173 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173 ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds ReferenceProfileData.CoarseLowerShape.Batch0021.a173.bounds
  · rw [←r_profile173_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile173_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry173_linked.2.2.2.2.1
  · exact geometry173_linked.2.2.2.2.2
  · exact r_reference173_checked
  · exact a_reference173_checked
  · exact r_fixed173_linked
  · exact a_fixed173_linked
  · exact time173_checked
  · exact ht
  · exact hw
theorem child_geometry173_checked : ReferenceWeightData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights173 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0043.cert346∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch43_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0043.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0043.cert347∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch43_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0043.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0043.cert346.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry173_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights346_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0043.cert347.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry173_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry173_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights347_linked j (List.mem_finRange j))
theorem actual_frozen_frame173 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame173 (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.flow.timeParameter_mem child_geometry173_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights173 hz)
theorem r_profile174_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r174=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds := by rfl
theorem a_profile174_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a174=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a174.bounds := by rfl
theorem r_fixed174_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 7 := by decide +kernel
theorem a_fixed174_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a174.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.a174.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 9 := by decide +kernel
theorem ranks174_linked : ReferenceRankData.CoarseLowerShape.Batch0021.targetR174=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0021.targetA174=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 1 := by decide +kernel
theorem r_input174_linked : ReferenceRankData.CoarseLowerShape.Batch0021.r174.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds.gauge] := by decide +kernel
theorem a_input174_linked : ReferenceRankData.CoarseLowerShape.Batch0021.a174.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.a174.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.a174.bounds.gauge] := by decide +kernel
theorem geometry174_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.a := by decide +kernel
theorem weights348_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0043.cert348.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights349_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0043.cert349.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time174_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 10)=true := by decide +kernel
theorem r_reference174_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 0)=true := by decide +kernel
theorem a_reference174_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 1)=true := by decide +kernel
theorem rank_r_link174_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r174 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link174_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0021.a174.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a174 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints174 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell true ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r174 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile174_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link174_checked
    geometry174_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell false ReferenceProfileData.CoarseLowerShape.Batch0021.a174.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a174 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile174_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link174_checked
    geometry174_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks174_linked.1,←ranks174_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0021.r174.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a174.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0021.ordered174_checked hr ha ho
theorem frozen_frame174 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174 ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds ReferenceProfileData.CoarseLowerShape.Batch0021.a174.bounds
  · rw [←r_profile174_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile174_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry174_linked.2.2.2.2.1
  · exact geometry174_linked.2.2.2.2.2
  · exact r_reference174_checked
  · exact a_reference174_checked
  · exact r_fixed174_linked
  · exact a_fixed174_linked
  · exact time174_checked
  · exact ht
  · exact hw
theorem child_geometry174_checked : ReferenceWeightData.CoarseLowerShape.Batch0043.cert348.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0043.cert348.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0043.cert349.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0043.cert349.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights174 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0043.cert348∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch43_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0043.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0043.cert349∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch43_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0043.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0043.cert348.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0043.cert348.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0043.cert348.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry174_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights348_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0043.cert349.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0043.cert349.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry174_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry174_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights349_linked j (List.mem_finRange j))
theorem actual_frozen_frame174 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame174 (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.flow.timeParameter_mem child_geometry174_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights174 hz)
theorem r_profile175_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r175=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds := by rfl
theorem a_profile175_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a175=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a175.bounds := by rfl
theorem r_fixed175_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 7 := by decide +kernel
theorem a_fixed175_linked : ReferenceProfileData.CoarseLowerShape.Batch0021.a175.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0021.a175.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 9 := by decide +kernel
theorem ranks175_linked : ReferenceRankData.CoarseLowerShape.Batch0021.targetR175=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0021.targetA175=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 1 := by decide +kernel
theorem r_input175_linked : ReferenceRankData.CoarseLowerShape.Batch0021.r175.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds.gauge] := by decide +kernel
theorem a_input175_linked : ReferenceRankData.CoarseLowerShape.Batch0021.a175.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0021.a175.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0021.a175.bounds.gauge] := by decide +kernel
theorem geometry175_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.a := by decide +kernel
theorem weights350_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0043.cert350.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights351_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0043.cert351.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time175_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 10)=true := by decide +kernel
theorem r_reference175_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 0)=true := by decide +kernel
theorem a_reference175_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 1)=true := by decide +kernel
theorem rank_r_link175_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r175 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link175_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0021.a175.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a175 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints175 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell true ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds ReferenceRankData.CoarseLowerShape.Batch0021.r175 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile175_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link175_checked
    geometry175_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell false ReferenceProfileData.CoarseLowerShape.Batch0021.a175.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a175 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile175_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0021.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0021.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link175_checked
    geometry175_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks175_linked.1,←ranks175_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0021.r175.bounds ReferenceRankData.CoarseLowerShape.Batch0021.a175.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0021.ordered175_checked hr ha ho
theorem frozen_frame175 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175 ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds ReferenceProfileData.CoarseLowerShape.Batch0021.a175.bounds
  · rw [←r_profile175_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile175_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry175_linked.2.2.2.2.1
  · exact geometry175_linked.2.2.2.2.2
  · exact r_reference175_checked
  · exact a_reference175_checked
  · exact r_fixed175_linked
  · exact a_fixed175_linked
  · exact time175_checked
  · exact ht
  · exact hw
theorem child_geometry175_checked : ReferenceWeightData.CoarseLowerShape.Batch0043.cert350.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0043.cert350.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0043.cert351.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0043.cert351.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights175 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0043.cert350∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch43_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0043.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0043.cert351∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch43_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0043.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0043.cert350.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0043.cert350.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0043.cert350.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry175_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights350_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0043.cert351.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0043.cert351.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry175_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry175_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights351_linked j (List.mem_finRange j))
theorem actual_frozen_frame175 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame175 (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.flow.timeParameter_mem child_geometry175_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights175 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell168),(ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell169),(ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell170),(ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell171),(ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell172),(ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell173),(ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell174),(ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0021.cell175)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0021.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0021.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame168 hz
  · exact fun z hz=>actual_frozen_frame169 hz
  · exact fun z hz=>actual_frozen_frame170 hz
  · exact fun z hz=>actual_frozen_frame171 hz
  · exact fun z hz=>actual_frozen_frame172 hz
  · exact fun z hz=>actual_frozen_frame173 hz
  · exact fun z hz=>actual_frozen_frame174 hz
  · exact fun z hz=>actual_frozen_frame175 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints168 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints169 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints170 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints171 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints172 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints173 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints174 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints175 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry168_linked.1,geometry168_linked.2.1,geometry168_linked.2.2.1,geometry168_linked.2.2.2.1⟩
  · exact ⟨geometry169_linked.1,geometry169_linked.2.1,geometry169_linked.2.2.1,geometry169_linked.2.2.2.1⟩
  · exact ⟨geometry170_linked.1,geometry170_linked.2.1,geometry170_linked.2.2.1,geometry170_linked.2.2.2.1⟩
  · exact ⟨geometry171_linked.1,geometry171_linked.2.1,geometry171_linked.2.2.1,geometry171_linked.2.2.2.1⟩
  · exact ⟨geometry172_linked.1,geometry172_linked.2.1,geometry172_linked.2.2.1,geometry172_linked.2.2.2.1⟩
  · exact ⟨geometry173_linked.1,geometry173_linked.2.1,geometry173_linked.2.2.1,geometry173_linked.2.2.2.1⟩
  · exact ⟨geometry174_linked.1,geometry174_linked.2.1,geometry174_linked.2.2.1,geometry174_linked.2.2.2.1⟩
  · exact ⟨geometry175_linked.1,geometry175_linked.2.1,geometry175_linked.2.2.1,geometry175_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.a168.bounds,?_,geometry168_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a168.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile168_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds,?_,geometry168_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert168.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r168.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile168_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.a169.bounds,?_,geometry169_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a169.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile169_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds,?_,geometry169_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert169.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r169.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile169_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.a170.bounds,?_,geometry170_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a170.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile170_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds,?_,geometry170_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert170.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r170.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile170_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.a171.bounds,?_,geometry171_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a171.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile171_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds,?_,geometry171_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert171.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r171.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile171_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.a172.bounds,?_,geometry172_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a172.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile172_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds,?_,geometry172_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert172.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r172.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile172_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.a173.bounds,?_,geometry173_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a173.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile173_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds,?_,geometry173_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert173.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r173.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile173_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.a174.bounds,?_,geometry174_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a174.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile174_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds,?_,geometry174_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert174.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r174.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile174_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.a175.bounds,?_,geometry175_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0021.a175.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile175_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds,?_,geometry175_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0021.cert175.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0021.r175.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile175_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0021.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0021.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0021

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0022
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch44_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0044.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0044.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch45_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0045.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0045.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile176_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r176=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds := by rfl
theorem a_profile176_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a176=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a176.bounds := by rfl
theorem r_fixed176_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 7 := by decide +kernel
theorem a_fixed176_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a176.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.a176.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 9 := by decide +kernel
theorem ranks176_linked : ReferenceRankData.CoarseLowerShape.Batch0022.targetR176=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0022.targetA176=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 1 := by decide +kernel
theorem r_input176_linked : ReferenceRankData.CoarseLowerShape.Batch0022.r176.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds.gauge] := by decide +kernel
theorem a_input176_linked : ReferenceRankData.CoarseLowerShape.Batch0022.a176.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.a176.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.a176.bounds.gauge] := by decide +kernel
theorem geometry176_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.a := by decide +kernel
theorem weights352_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0044.cert352.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights353_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0044.cert353.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time176_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 10)=true := by decide +kernel
theorem r_reference176_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 0)=true := by decide +kernel
theorem a_reference176_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 1)=true := by decide +kernel
theorem rank_r_link176_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r176 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link176_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0022.a176.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a176 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints176 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell true ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r176 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile176_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link176_checked
    geometry176_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell false ReferenceProfileData.CoarseLowerShape.Batch0022.a176.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a176 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile176_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link176_checked
    geometry176_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks176_linked.1,←ranks176_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0022.r176.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a176.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0022.ordered176_checked hr ha ho
theorem frozen_frame176 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176 ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds ReferenceProfileData.CoarseLowerShape.Batch0022.a176.bounds
  · rw [←r_profile176_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile176_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry176_linked.2.2.2.2.1
  · exact geometry176_linked.2.2.2.2.2
  · exact r_reference176_checked
  · exact a_reference176_checked
  · exact r_fixed176_linked
  · exact a_fixed176_linked
  · exact time176_checked
  · exact ht
  · exact hw
theorem child_geometry176_checked : ReferenceWeightData.CoarseLowerShape.Batch0044.cert352.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0044.cert352.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0044.cert353.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0044.cert353.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights176 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0044.cert352∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch44_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0044.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0044.cert353∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch44_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0044.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0044.cert352.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0044.cert352.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0044.cert352.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry176_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights352_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0044.cert353.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0044.cert353.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry176_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry176_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights353_linked j (List.mem_finRange j))
theorem actual_frozen_frame176 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame176 (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.flow.timeParameter_mem child_geometry176_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights176 hz)
theorem r_profile177_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r177=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds := by rfl
theorem a_profile177_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a177=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a177.bounds := by rfl
theorem r_fixed177_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 7 := by decide +kernel
theorem a_fixed177_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a177.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.a177.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 9 := by decide +kernel
theorem ranks177_linked : ReferenceRankData.CoarseLowerShape.Batch0022.targetR177=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0022.targetA177=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 1 := by decide +kernel
theorem r_input177_linked : ReferenceRankData.CoarseLowerShape.Batch0022.r177.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds.gauge] := by decide +kernel
theorem a_input177_linked : ReferenceRankData.CoarseLowerShape.Batch0022.a177.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.a177.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.a177.bounds.gauge] := by decide +kernel
theorem geometry177_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.a := by decide +kernel
theorem weights354_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0044.cert354.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights355_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0044.cert355.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time177_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 10)=true := by decide +kernel
theorem r_reference177_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 0)=true := by decide +kernel
theorem a_reference177_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 1)=true := by decide +kernel
theorem rank_r_link177_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r177 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link177_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0022.a177.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a177 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints177 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell true ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r177 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile177_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link177_checked
    geometry177_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell false ReferenceProfileData.CoarseLowerShape.Batch0022.a177.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a177 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile177_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link177_checked
    geometry177_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks177_linked.1,←ranks177_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0022.r177.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a177.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0022.ordered177_checked hr ha ho
theorem frozen_frame177 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177 ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds ReferenceProfileData.CoarseLowerShape.Batch0022.a177.bounds
  · rw [←r_profile177_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile177_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry177_linked.2.2.2.2.1
  · exact geometry177_linked.2.2.2.2.2
  · exact r_reference177_checked
  · exact a_reference177_checked
  · exact r_fixed177_linked
  · exact a_fixed177_linked
  · exact time177_checked
  · exact ht
  · exact hw
theorem child_geometry177_checked : ReferenceWeightData.CoarseLowerShape.Batch0044.cert354.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0044.cert354.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0044.cert355.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0044.cert355.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights177 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0044.cert354∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch44_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0044.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0044.cert355∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch44_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0044.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0044.cert354.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0044.cert354.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0044.cert354.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry177_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights354_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0044.cert355.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0044.cert355.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry177_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry177_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights355_linked j (List.mem_finRange j))
theorem actual_frozen_frame177 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame177 (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.flow.timeParameter_mem child_geometry177_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights177 hz)
theorem r_profile178_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r178=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds := by rfl
theorem a_profile178_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a178=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a178.bounds := by rfl
theorem r_fixed178_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 7 := by decide +kernel
theorem a_fixed178_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a178.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.a178.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 9 := by decide +kernel
theorem ranks178_linked : ReferenceRankData.CoarseLowerShape.Batch0022.targetR178=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0022.targetA178=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 1 := by decide +kernel
theorem r_input178_linked : ReferenceRankData.CoarseLowerShape.Batch0022.r178.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds.gauge] := by decide +kernel
theorem a_input178_linked : ReferenceRankData.CoarseLowerShape.Batch0022.a178.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.a178.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.a178.bounds.gauge] := by decide +kernel
theorem geometry178_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.a := by decide +kernel
theorem weights356_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0044.cert356.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights357_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0044.cert357.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time178_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 10)=true := by decide +kernel
theorem r_reference178_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 0)=true := by decide +kernel
theorem a_reference178_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 1)=true := by decide +kernel
theorem rank_r_link178_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r178 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link178_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0022.a178.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a178 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints178 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell true ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r178 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile178_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link178_checked
    geometry178_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell false ReferenceProfileData.CoarseLowerShape.Batch0022.a178.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a178 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile178_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link178_checked
    geometry178_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks178_linked.1,←ranks178_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0022.r178.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a178.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0022.ordered178_checked hr ha ho
theorem frozen_frame178 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178 ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds ReferenceProfileData.CoarseLowerShape.Batch0022.a178.bounds
  · rw [←r_profile178_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile178_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry178_linked.2.2.2.2.1
  · exact geometry178_linked.2.2.2.2.2
  · exact r_reference178_checked
  · exact a_reference178_checked
  · exact r_fixed178_linked
  · exact a_fixed178_linked
  · exact time178_checked
  · exact ht
  · exact hw
theorem child_geometry178_checked : ReferenceWeightData.CoarseLowerShape.Batch0044.cert356.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0044.cert356.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0044.cert357.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0044.cert357.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights178 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0044.cert356∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch44_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0044.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0044.cert357∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch44_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0044.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0044.cert356.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0044.cert356.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0044.cert356.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry178_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights356_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0044.cert357.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0044.cert357.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry178_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry178_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights357_linked j (List.mem_finRange j))
theorem actual_frozen_frame178 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame178 (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.flow.timeParameter_mem child_geometry178_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights178 hz)
theorem r_profile179_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r179=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds := by rfl
theorem a_profile179_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a179=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a179.bounds := by rfl
theorem r_fixed179_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 7 := by decide +kernel
theorem a_fixed179_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a179.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.a179.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 9 := by decide +kernel
theorem ranks179_linked : ReferenceRankData.CoarseLowerShape.Batch0022.targetR179=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0022.targetA179=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 1 := by decide +kernel
theorem r_input179_linked : ReferenceRankData.CoarseLowerShape.Batch0022.r179.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds.gauge] := by decide +kernel
theorem a_input179_linked : ReferenceRankData.CoarseLowerShape.Batch0022.a179.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.a179.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.a179.bounds.gauge] := by decide +kernel
theorem geometry179_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.a := by decide +kernel
theorem weights358_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0044.cert358.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights359_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0044.cert359.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time179_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 10)=true := by decide +kernel
theorem r_reference179_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 0)=true := by decide +kernel
theorem a_reference179_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 1)=true := by decide +kernel
theorem rank_r_link179_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r179 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link179_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0022.a179.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a179 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints179 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell true ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r179 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile179_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link179_checked
    geometry179_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell false ReferenceProfileData.CoarseLowerShape.Batch0022.a179.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a179 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile179_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link179_checked
    geometry179_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks179_linked.1,←ranks179_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0022.r179.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a179.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0022.ordered179_checked hr ha ho
theorem frozen_frame179 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179 ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds ReferenceProfileData.CoarseLowerShape.Batch0022.a179.bounds
  · rw [←r_profile179_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile179_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry179_linked.2.2.2.2.1
  · exact geometry179_linked.2.2.2.2.2
  · exact r_reference179_checked
  · exact a_reference179_checked
  · exact r_fixed179_linked
  · exact a_fixed179_linked
  · exact time179_checked
  · exact ht
  · exact hw
theorem child_geometry179_checked : ReferenceWeightData.CoarseLowerShape.Batch0044.cert358.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0044.cert358.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0044.cert359.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0044.cert359.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights179 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0044.cert358∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch44_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0044.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0044.cert359∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch44_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0044.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0044.cert358.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0044.cert358.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0044.cert358.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry179_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights358_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0044.cert359.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0044.cert359.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry179_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry179_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights359_linked j (List.mem_finRange j))
theorem actual_frozen_frame179 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame179 (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.flow.timeParameter_mem child_geometry179_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights179 hz)
theorem r_profile180_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r180=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds := by rfl
theorem a_profile180_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a180=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a180.bounds := by rfl
theorem r_fixed180_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 7 := by decide +kernel
theorem a_fixed180_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a180.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.a180.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 9 := by decide +kernel
theorem ranks180_linked : ReferenceRankData.CoarseLowerShape.Batch0022.targetR180=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0022.targetA180=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 1 := by decide +kernel
theorem r_input180_linked : ReferenceRankData.CoarseLowerShape.Batch0022.r180.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds.gauge] := by decide +kernel
theorem a_input180_linked : ReferenceRankData.CoarseLowerShape.Batch0022.a180.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.a180.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.a180.bounds.gauge] := by decide +kernel
theorem geometry180_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.a := by decide +kernel
theorem weights360_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0045.cert360.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights361_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0045.cert361.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time180_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 10)=true := by decide +kernel
theorem r_reference180_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 0)=true := by decide +kernel
theorem a_reference180_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 1)=true := by decide +kernel
theorem rank_r_link180_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r180 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link180_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0022.a180.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a180 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints180 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell true ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r180 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile180_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link180_checked
    geometry180_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell false ReferenceProfileData.CoarseLowerShape.Batch0022.a180.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a180 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile180_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link180_checked
    geometry180_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks180_linked.1,←ranks180_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0022.r180.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a180.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0022.ordered180_checked hr ha ho
theorem frozen_frame180 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180 ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds ReferenceProfileData.CoarseLowerShape.Batch0022.a180.bounds
  · rw [←r_profile180_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile180_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry180_linked.2.2.2.2.1
  · exact geometry180_linked.2.2.2.2.2
  · exact r_reference180_checked
  · exact a_reference180_checked
  · exact r_fixed180_linked
  · exact a_fixed180_linked
  · exact time180_checked
  · exact ht
  · exact hw
theorem child_geometry180_checked : ReferenceWeightData.CoarseLowerShape.Batch0045.cert360.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0045.cert360.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0045.cert361.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0045.cert361.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights180 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0045.cert360∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch45_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0045.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0045.cert361∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch45_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0045.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0045.cert360.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0045.cert360.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0045.cert360.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry180_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights360_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0045.cert361.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0045.cert361.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry180_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry180_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights361_linked j (List.mem_finRange j))
theorem actual_frozen_frame180 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame180 (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.flow.timeParameter_mem child_geometry180_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights180 hz)
theorem r_profile181_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r181=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds := by rfl
theorem a_profile181_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a181=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a181.bounds := by rfl
theorem r_fixed181_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 7 := by decide +kernel
theorem a_fixed181_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a181.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.a181.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 9 := by decide +kernel
theorem ranks181_linked : ReferenceRankData.CoarseLowerShape.Batch0022.targetR181=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0022.targetA181=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 1 := by decide +kernel
theorem r_input181_linked : ReferenceRankData.CoarseLowerShape.Batch0022.r181.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds.gauge] := by decide +kernel
theorem a_input181_linked : ReferenceRankData.CoarseLowerShape.Batch0022.a181.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.a181.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.a181.bounds.gauge] := by decide +kernel
theorem geometry181_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.a := by decide +kernel
theorem weights362_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0045.cert362.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights363_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0045.cert363.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time181_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 10)=true := by decide +kernel
theorem r_reference181_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 0)=true := by decide +kernel
theorem a_reference181_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 1)=true := by decide +kernel
theorem rank_r_link181_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r181 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link181_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0022.a181.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a181 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints181 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell true ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r181 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile181_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link181_checked
    geometry181_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell false ReferenceProfileData.CoarseLowerShape.Batch0022.a181.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a181 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile181_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link181_checked
    geometry181_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks181_linked.1,←ranks181_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0022.r181.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a181.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0022.ordered181_checked hr ha ho
theorem frozen_frame181 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181 ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds ReferenceProfileData.CoarseLowerShape.Batch0022.a181.bounds
  · rw [←r_profile181_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile181_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry181_linked.2.2.2.2.1
  · exact geometry181_linked.2.2.2.2.2
  · exact r_reference181_checked
  · exact a_reference181_checked
  · exact r_fixed181_linked
  · exact a_fixed181_linked
  · exact time181_checked
  · exact ht
  · exact hw
theorem child_geometry181_checked : ReferenceWeightData.CoarseLowerShape.Batch0045.cert362.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0045.cert362.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0045.cert363.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0045.cert363.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights181 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0045.cert362∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch45_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0045.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0045.cert363∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch45_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0045.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0045.cert362.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0045.cert362.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0045.cert362.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry181_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights362_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0045.cert363.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0045.cert363.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry181_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry181_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights363_linked j (List.mem_finRange j))
theorem actual_frozen_frame181 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame181 (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.flow.timeParameter_mem child_geometry181_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights181 hz)
theorem r_profile182_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r182=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds := by rfl
theorem a_profile182_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a182=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a182.bounds := by rfl
theorem r_fixed182_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 7 := by decide +kernel
theorem a_fixed182_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a182.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.a182.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 9 := by decide +kernel
theorem ranks182_linked : ReferenceRankData.CoarseLowerShape.Batch0022.targetR182=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0022.targetA182=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 1 := by decide +kernel
theorem r_input182_linked : ReferenceRankData.CoarseLowerShape.Batch0022.r182.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds.gauge] := by decide +kernel
theorem a_input182_linked : ReferenceRankData.CoarseLowerShape.Batch0022.a182.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.a182.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.a182.bounds.gauge] := by decide +kernel
theorem geometry182_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.a := by decide +kernel
theorem weights364_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0045.cert364.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights365_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0045.cert365.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time182_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 10)=true := by decide +kernel
theorem r_reference182_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 0)=true := by decide +kernel
theorem a_reference182_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 1)=true := by decide +kernel
theorem rank_r_link182_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r182 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link182_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0022.a182.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a182 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints182 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell true ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r182 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile182_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link182_checked
    geometry182_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell false ReferenceProfileData.CoarseLowerShape.Batch0022.a182.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a182 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile182_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link182_checked
    geometry182_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks182_linked.1,←ranks182_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0022.r182.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a182.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0022.ordered182_checked hr ha ho
theorem frozen_frame182 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182 ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds ReferenceProfileData.CoarseLowerShape.Batch0022.a182.bounds
  · rw [←r_profile182_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile182_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry182_linked.2.2.2.2.1
  · exact geometry182_linked.2.2.2.2.2
  · exact r_reference182_checked
  · exact a_reference182_checked
  · exact r_fixed182_linked
  · exact a_fixed182_linked
  · exact time182_checked
  · exact ht
  · exact hw
theorem child_geometry182_checked : ReferenceWeightData.CoarseLowerShape.Batch0045.cert364.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0045.cert364.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0045.cert365.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0045.cert365.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights182 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0045.cert364∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch45_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0045.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0045.cert365∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch45_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0045.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0045.cert364.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0045.cert364.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0045.cert364.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry182_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights364_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0045.cert365.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0045.cert365.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry182_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry182_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights365_linked j (List.mem_finRange j))
theorem actual_frozen_frame182 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame182 (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.flow.timeParameter_mem child_geometry182_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights182 hz)
theorem r_profile183_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r183=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds := by rfl
theorem a_profile183_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a183=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a183.bounds := by rfl
theorem r_fixed183_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 7 := by decide +kernel
theorem a_fixed183_linked : ReferenceProfileData.CoarseLowerShape.Batch0022.a183.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0022.a183.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 9 := by decide +kernel
theorem ranks183_linked : ReferenceRankData.CoarseLowerShape.Batch0022.targetR183=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0022.targetA183=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 1 := by decide +kernel
theorem r_input183_linked : ReferenceRankData.CoarseLowerShape.Batch0022.r183.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds.gauge] := by decide +kernel
theorem a_input183_linked : ReferenceRankData.CoarseLowerShape.Batch0022.a183.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0022.a183.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0022.a183.bounds.gauge] := by decide +kernel
theorem geometry183_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.a := by decide +kernel
theorem weights366_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0045.cert366.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights367_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0045.cert367.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time183_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 10)=true := by decide +kernel
theorem r_reference183_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 0)=true := by decide +kernel
theorem a_reference183_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 1)=true := by decide +kernel
theorem rank_r_link183_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r183 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link183_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0022.a183.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a183 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints183 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell true ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds ReferenceRankData.CoarseLowerShape.Batch0022.r183 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile183_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link183_checked
    geometry183_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell false ReferenceProfileData.CoarseLowerShape.Batch0022.a183.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a183 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile183_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0022.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0022.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link183_checked
    geometry183_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks183_linked.1,←ranks183_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0022.r183.bounds ReferenceRankData.CoarseLowerShape.Batch0022.a183.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0022.ordered183_checked hr ha ho
theorem frozen_frame183 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183 ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds ReferenceProfileData.CoarseLowerShape.Batch0022.a183.bounds
  · rw [←r_profile183_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile183_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry183_linked.2.2.2.2.1
  · exact geometry183_linked.2.2.2.2.2
  · exact r_reference183_checked
  · exact a_reference183_checked
  · exact r_fixed183_linked
  · exact a_fixed183_linked
  · exact time183_checked
  · exact ht
  · exact hw
theorem child_geometry183_checked : ReferenceWeightData.CoarseLowerShape.Batch0045.cert366.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0045.cert366.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0045.cert367.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0045.cert367.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights183 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0045.cert366∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch45_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0045.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0045.cert367∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch45_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0045.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0045.cert366.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0045.cert366.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0045.cert366.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry183_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights366_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0045.cert367.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0045.cert367.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry183_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry183_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights367_linked j (List.mem_finRange j))
theorem actual_frozen_frame183 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame183 (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.flow.timeParameter_mem child_geometry183_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights183 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell176),(ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell177),(ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell178),(ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell179),(ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell180),(ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell181),(ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell182),(ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0022.cell183)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0022.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0022.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame176 hz
  · exact fun z hz=>actual_frozen_frame177 hz
  · exact fun z hz=>actual_frozen_frame178 hz
  · exact fun z hz=>actual_frozen_frame179 hz
  · exact fun z hz=>actual_frozen_frame180 hz
  · exact fun z hz=>actual_frozen_frame181 hz
  · exact fun z hz=>actual_frozen_frame182 hz
  · exact fun z hz=>actual_frozen_frame183 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints176 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints177 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints178 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints179 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints180 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints181 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints182 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints183 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry176_linked.1,geometry176_linked.2.1,geometry176_linked.2.2.1,geometry176_linked.2.2.2.1⟩
  · exact ⟨geometry177_linked.1,geometry177_linked.2.1,geometry177_linked.2.2.1,geometry177_linked.2.2.2.1⟩
  · exact ⟨geometry178_linked.1,geometry178_linked.2.1,geometry178_linked.2.2.1,geometry178_linked.2.2.2.1⟩
  · exact ⟨geometry179_linked.1,geometry179_linked.2.1,geometry179_linked.2.2.1,geometry179_linked.2.2.2.1⟩
  · exact ⟨geometry180_linked.1,geometry180_linked.2.1,geometry180_linked.2.2.1,geometry180_linked.2.2.2.1⟩
  · exact ⟨geometry181_linked.1,geometry181_linked.2.1,geometry181_linked.2.2.1,geometry181_linked.2.2.2.1⟩
  · exact ⟨geometry182_linked.1,geometry182_linked.2.1,geometry182_linked.2.2.1,geometry182_linked.2.2.2.1⟩
  · exact ⟨geometry183_linked.1,geometry183_linked.2.1,geometry183_linked.2.2.1,geometry183_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.a176.bounds,?_,geometry176_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a176.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile176_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds,?_,geometry176_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert176.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r176.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile176_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.a177.bounds,?_,geometry177_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a177.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile177_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds,?_,geometry177_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert177.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r177.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile177_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.a178.bounds,?_,geometry178_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a178.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile178_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds,?_,geometry178_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert178.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r178.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile178_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.a179.bounds,?_,geometry179_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a179.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile179_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds,?_,geometry179_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert179.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r179.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile179_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.a180.bounds,?_,geometry180_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a180.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile180_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds,?_,geometry180_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert180.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r180.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile180_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.a181.bounds,?_,geometry181_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a181.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile181_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds,?_,geometry181_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert181.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r181.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile181_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.a182.bounds,?_,geometry182_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a182.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile182_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds,?_,geometry182_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert182.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r182.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile182_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.a183.bounds,?_,geometry183_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0022.a183.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile183_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds,?_,geometry183_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0022.cert183.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0022.r183.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile183_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0022.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0022.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0022

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0023
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch46_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0046.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0046.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch47_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0047.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0047.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile184_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r184=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds := by rfl
theorem a_profile184_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a184=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a184.bounds := by rfl
theorem r_fixed184_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 7 := by decide +kernel
theorem a_fixed184_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a184.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.a184.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 9 := by decide +kernel
theorem ranks184_linked : ReferenceRankData.CoarseLowerShape.Batch0023.targetR184=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0023.targetA184=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 1 := by decide +kernel
theorem r_input184_linked : ReferenceRankData.CoarseLowerShape.Batch0023.r184.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds.gauge] := by decide +kernel
theorem a_input184_linked : ReferenceRankData.CoarseLowerShape.Batch0023.a184.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.a184.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.a184.bounds.gauge] := by decide +kernel
theorem geometry184_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.a := by decide +kernel
theorem weights368_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0046.cert368.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights369_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0046.cert369.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time184_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 10)=true := by decide +kernel
theorem r_reference184_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 0)=true := by decide +kernel
theorem a_reference184_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 1)=true := by decide +kernel
theorem rank_r_link184_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r184 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link184_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0023.a184.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a184 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints184 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell true ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r184 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile184_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link184_checked
    geometry184_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell false ReferenceProfileData.CoarseLowerShape.Batch0023.a184.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a184 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile184_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link184_checked
    geometry184_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks184_linked.1,←ranks184_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0023.r184.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a184.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0023.ordered184_checked hr ha ho
theorem frozen_frame184 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184 ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds ReferenceProfileData.CoarseLowerShape.Batch0023.a184.bounds
  · rw [←r_profile184_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile184_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry184_linked.2.2.2.2.1
  · exact geometry184_linked.2.2.2.2.2
  · exact r_reference184_checked
  · exact a_reference184_checked
  · exact r_fixed184_linked
  · exact a_fixed184_linked
  · exact time184_checked
  · exact ht
  · exact hw
theorem child_geometry184_checked : ReferenceWeightData.CoarseLowerShape.Batch0046.cert368.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0046.cert368.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0046.cert369.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0046.cert369.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights184 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0046.cert368∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch46_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0046.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0046.cert369∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch46_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0046.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0046.cert368.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0046.cert368.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0046.cert368.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry184_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights368_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0046.cert369.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0046.cert369.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry184_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry184_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights369_linked j (List.mem_finRange j))
theorem actual_frozen_frame184 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame184 (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.flow.timeParameter_mem child_geometry184_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights184 hz)
theorem r_profile185_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r185=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds := by rfl
theorem a_profile185_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a185=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a185.bounds := by rfl
theorem r_fixed185_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 7 := by decide +kernel
theorem a_fixed185_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a185.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.a185.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 9 := by decide +kernel
theorem ranks185_linked : ReferenceRankData.CoarseLowerShape.Batch0023.targetR185=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0023.targetA185=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 1 := by decide +kernel
theorem r_input185_linked : ReferenceRankData.CoarseLowerShape.Batch0023.r185.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds.gauge] := by decide +kernel
theorem a_input185_linked : ReferenceRankData.CoarseLowerShape.Batch0023.a185.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.a185.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.a185.bounds.gauge] := by decide +kernel
theorem geometry185_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.a := by decide +kernel
theorem weights370_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0046.cert370.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights371_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0046.cert371.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time185_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 10)=true := by decide +kernel
theorem r_reference185_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 0)=true := by decide +kernel
theorem a_reference185_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 1)=true := by decide +kernel
theorem rank_r_link185_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r185 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link185_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0023.a185.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a185 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints185 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell true ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r185 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile185_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link185_checked
    geometry185_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell false ReferenceProfileData.CoarseLowerShape.Batch0023.a185.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a185 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile185_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link185_checked
    geometry185_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks185_linked.1,←ranks185_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0023.r185.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a185.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0023.ordered185_checked hr ha ho
theorem frozen_frame185 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185 ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds ReferenceProfileData.CoarseLowerShape.Batch0023.a185.bounds
  · rw [←r_profile185_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile185_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry185_linked.2.2.2.2.1
  · exact geometry185_linked.2.2.2.2.2
  · exact r_reference185_checked
  · exact a_reference185_checked
  · exact r_fixed185_linked
  · exact a_fixed185_linked
  · exact time185_checked
  · exact ht
  · exact hw
theorem child_geometry185_checked : ReferenceWeightData.CoarseLowerShape.Batch0046.cert370.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0046.cert370.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0046.cert371.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0046.cert371.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights185 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0046.cert370∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch46_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0046.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0046.cert371∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch46_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0046.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0046.cert370.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0046.cert370.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0046.cert370.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry185_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights370_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0046.cert371.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0046.cert371.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry185_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry185_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights371_linked j (List.mem_finRange j))
theorem actual_frozen_frame185 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame185 (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.flow.timeParameter_mem child_geometry185_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights185 hz)
theorem r_profile186_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r186=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds := by rfl
theorem a_profile186_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a186=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a186.bounds := by rfl
theorem r_fixed186_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 7 := by decide +kernel
theorem a_fixed186_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a186.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.a186.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 9 := by decide +kernel
theorem ranks186_linked : ReferenceRankData.CoarseLowerShape.Batch0023.targetR186=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0023.targetA186=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 1 := by decide +kernel
theorem r_input186_linked : ReferenceRankData.CoarseLowerShape.Batch0023.r186.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds.gauge] := by decide +kernel
theorem a_input186_linked : ReferenceRankData.CoarseLowerShape.Batch0023.a186.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.a186.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.a186.bounds.gauge] := by decide +kernel
theorem geometry186_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.a := by decide +kernel
theorem weights372_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0046.cert372.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights373_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0046.cert373.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time186_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 10)=true := by decide +kernel
theorem r_reference186_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 0)=true := by decide +kernel
theorem a_reference186_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 1)=true := by decide +kernel
theorem rank_r_link186_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r186 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link186_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0023.a186.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a186 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints186 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell true ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r186 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile186_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link186_checked
    geometry186_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell false ReferenceProfileData.CoarseLowerShape.Batch0023.a186.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a186 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile186_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link186_checked
    geometry186_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks186_linked.1,←ranks186_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0023.r186.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a186.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0023.ordered186_checked hr ha ho
theorem frozen_frame186 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186 ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds ReferenceProfileData.CoarseLowerShape.Batch0023.a186.bounds
  · rw [←r_profile186_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile186_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry186_linked.2.2.2.2.1
  · exact geometry186_linked.2.2.2.2.2
  · exact r_reference186_checked
  · exact a_reference186_checked
  · exact r_fixed186_linked
  · exact a_fixed186_linked
  · exact time186_checked
  · exact ht
  · exact hw
theorem child_geometry186_checked : ReferenceWeightData.CoarseLowerShape.Batch0046.cert372.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0046.cert372.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0046.cert373.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0046.cert373.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights186 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0046.cert372∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch46_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0046.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0046.cert373∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch46_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0046.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0046.cert372.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0046.cert372.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0046.cert372.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry186_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights372_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0046.cert373.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0046.cert373.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry186_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry186_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights373_linked j (List.mem_finRange j))
theorem actual_frozen_frame186 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame186 (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.flow.timeParameter_mem child_geometry186_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights186 hz)
theorem r_profile187_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r187=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds := by rfl
theorem a_profile187_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a187=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a187.bounds := by rfl
theorem r_fixed187_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 7 := by decide +kernel
theorem a_fixed187_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a187.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.a187.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 9 := by decide +kernel
theorem ranks187_linked : ReferenceRankData.CoarseLowerShape.Batch0023.targetR187=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0023.targetA187=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 1 := by decide +kernel
theorem r_input187_linked : ReferenceRankData.CoarseLowerShape.Batch0023.r187.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds.gauge] := by decide +kernel
theorem a_input187_linked : ReferenceRankData.CoarseLowerShape.Batch0023.a187.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.a187.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.a187.bounds.gauge] := by decide +kernel
theorem geometry187_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.a := by decide +kernel
theorem weights374_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0046.cert374.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights375_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0046.cert375.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time187_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 10)=true := by decide +kernel
theorem r_reference187_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 0)=true := by decide +kernel
theorem a_reference187_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 1)=true := by decide +kernel
theorem rank_r_link187_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r187 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link187_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0023.a187.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a187 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints187 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell true ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r187 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile187_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link187_checked
    geometry187_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell false ReferenceProfileData.CoarseLowerShape.Batch0023.a187.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a187 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile187_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link187_checked
    geometry187_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks187_linked.1,←ranks187_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0023.r187.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a187.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0023.ordered187_checked hr ha ho
theorem frozen_frame187 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187 ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds ReferenceProfileData.CoarseLowerShape.Batch0023.a187.bounds
  · rw [←r_profile187_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile187_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry187_linked.2.2.2.2.1
  · exact geometry187_linked.2.2.2.2.2
  · exact r_reference187_checked
  · exact a_reference187_checked
  · exact r_fixed187_linked
  · exact a_fixed187_linked
  · exact time187_checked
  · exact ht
  · exact hw
theorem child_geometry187_checked : ReferenceWeightData.CoarseLowerShape.Batch0046.cert374.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0046.cert374.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0046.cert375.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0046.cert375.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights187 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0046.cert374∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch46_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0046.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0046.cert375∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch46_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0046.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0046.cert374.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0046.cert374.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0046.cert374.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry187_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights374_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0046.cert375.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0046.cert375.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry187_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry187_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights375_linked j (List.mem_finRange j))
theorem actual_frozen_frame187 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame187 (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.flow.timeParameter_mem child_geometry187_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights187 hz)
theorem r_profile188_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r188=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds := by rfl
theorem a_profile188_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a188=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a188.bounds := by rfl
theorem r_fixed188_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 7 := by decide +kernel
theorem a_fixed188_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a188.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.a188.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 9 := by decide +kernel
theorem ranks188_linked : ReferenceRankData.CoarseLowerShape.Batch0023.targetR188=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0023.targetA188=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 1 := by decide +kernel
theorem r_input188_linked : ReferenceRankData.CoarseLowerShape.Batch0023.r188.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds.gauge] := by decide +kernel
theorem a_input188_linked : ReferenceRankData.CoarseLowerShape.Batch0023.a188.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.a188.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.a188.bounds.gauge] := by decide +kernel
theorem geometry188_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.a := by decide +kernel
theorem weights376_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0047.cert376.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights377_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0047.cert377.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time188_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 10)=true := by decide +kernel
theorem r_reference188_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 0)=true := by decide +kernel
theorem a_reference188_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 1)=true := by decide +kernel
theorem rank_r_link188_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r188 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link188_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0023.a188.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a188 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints188 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell true ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r188 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile188_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link188_checked
    geometry188_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell false ReferenceProfileData.CoarseLowerShape.Batch0023.a188.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a188 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile188_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link188_checked
    geometry188_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks188_linked.1,←ranks188_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0023.r188.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a188.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0023.ordered188_checked hr ha ho
theorem frozen_frame188 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188 ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds ReferenceProfileData.CoarseLowerShape.Batch0023.a188.bounds
  · rw [←r_profile188_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile188_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry188_linked.2.2.2.2.1
  · exact geometry188_linked.2.2.2.2.2
  · exact r_reference188_checked
  · exact a_reference188_checked
  · exact r_fixed188_linked
  · exact a_fixed188_linked
  · exact time188_checked
  · exact ht
  · exact hw
theorem child_geometry188_checked : ReferenceWeightData.CoarseLowerShape.Batch0047.cert376.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0047.cert376.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0047.cert377.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0047.cert377.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights188 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0047.cert376∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch47_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0047.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0047.cert377∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch47_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0047.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0047.cert376.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0047.cert376.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0047.cert376.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry188_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights376_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0047.cert377.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0047.cert377.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry188_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry188_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights377_linked j (List.mem_finRange j))
theorem actual_frozen_frame188 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame188 (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.flow.timeParameter_mem child_geometry188_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights188 hz)
theorem r_profile189_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r189=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds := by rfl
theorem a_profile189_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a189=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a189.bounds := by rfl
theorem r_fixed189_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 7 := by decide +kernel
theorem a_fixed189_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a189.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.a189.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 9 := by decide +kernel
theorem ranks189_linked : ReferenceRankData.CoarseLowerShape.Batch0023.targetR189=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0023.targetA189=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 1 := by decide +kernel
theorem r_input189_linked : ReferenceRankData.CoarseLowerShape.Batch0023.r189.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds.gauge] := by decide +kernel
theorem a_input189_linked : ReferenceRankData.CoarseLowerShape.Batch0023.a189.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.a189.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.a189.bounds.gauge] := by decide +kernel
theorem geometry189_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.a := by decide +kernel
theorem weights378_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0047.cert378.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights379_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0047.cert379.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time189_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 10)=true := by decide +kernel
theorem r_reference189_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 0)=true := by decide +kernel
theorem a_reference189_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 1)=true := by decide +kernel
theorem rank_r_link189_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r189 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link189_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0023.a189.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a189 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints189 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell true ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r189 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile189_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link189_checked
    geometry189_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell false ReferenceProfileData.CoarseLowerShape.Batch0023.a189.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a189 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile189_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link189_checked
    geometry189_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks189_linked.1,←ranks189_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0023.r189.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a189.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0023.ordered189_checked hr ha ho
theorem frozen_frame189 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189 ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds ReferenceProfileData.CoarseLowerShape.Batch0023.a189.bounds
  · rw [←r_profile189_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile189_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry189_linked.2.2.2.2.1
  · exact geometry189_linked.2.2.2.2.2
  · exact r_reference189_checked
  · exact a_reference189_checked
  · exact r_fixed189_linked
  · exact a_fixed189_linked
  · exact time189_checked
  · exact ht
  · exact hw
theorem child_geometry189_checked : ReferenceWeightData.CoarseLowerShape.Batch0047.cert378.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0047.cert378.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0047.cert379.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0047.cert379.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights189 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0047.cert378∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch47_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0047.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0047.cert379∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch47_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0047.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0047.cert378.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0047.cert378.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0047.cert378.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry189_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights378_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0047.cert379.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0047.cert379.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry189_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry189_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights379_linked j (List.mem_finRange j))
theorem actual_frozen_frame189 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame189 (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.flow.timeParameter_mem child_geometry189_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights189 hz)
theorem r_profile190_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r190=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds := by rfl
theorem a_profile190_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a190=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a190.bounds := by rfl
theorem r_fixed190_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 7 := by decide +kernel
theorem a_fixed190_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a190.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.a190.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 9 := by decide +kernel
theorem ranks190_linked : ReferenceRankData.CoarseLowerShape.Batch0023.targetR190=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0023.targetA190=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 1 := by decide +kernel
theorem r_input190_linked : ReferenceRankData.CoarseLowerShape.Batch0023.r190.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds.gauge] := by decide +kernel
theorem a_input190_linked : ReferenceRankData.CoarseLowerShape.Batch0023.a190.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.a190.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.a190.bounds.gauge] := by decide +kernel
theorem geometry190_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.a := by decide +kernel
theorem weights380_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0047.cert380.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights381_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0047.cert381.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time190_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 10)=true := by decide +kernel
theorem r_reference190_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 0)=true := by decide +kernel
theorem a_reference190_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 1)=true := by decide +kernel
theorem rank_r_link190_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r190 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link190_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0023.a190.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a190 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints190 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell true ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r190 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile190_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link190_checked
    geometry190_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell false ReferenceProfileData.CoarseLowerShape.Batch0023.a190.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a190 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile190_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link190_checked
    geometry190_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks190_linked.1,←ranks190_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0023.r190.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a190.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0023.ordered190_checked hr ha ho
theorem frozen_frame190 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190 ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds ReferenceProfileData.CoarseLowerShape.Batch0023.a190.bounds
  · rw [←r_profile190_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile190_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry190_linked.2.2.2.2.1
  · exact geometry190_linked.2.2.2.2.2
  · exact r_reference190_checked
  · exact a_reference190_checked
  · exact r_fixed190_linked
  · exact a_fixed190_linked
  · exact time190_checked
  · exact ht
  · exact hw
theorem child_geometry190_checked : ReferenceWeightData.CoarseLowerShape.Batch0047.cert380.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0047.cert380.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0047.cert381.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0047.cert381.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights190 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0047.cert380∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch47_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0047.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0047.cert381∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch47_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0047.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0047.cert380.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0047.cert380.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0047.cert380.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry190_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights380_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0047.cert381.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0047.cert381.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry190_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry190_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights381_linked j (List.mem_finRange j))
theorem actual_frozen_frame190 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame190 (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.flow.timeParameter_mem child_geometry190_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights190 hz)
theorem r_profile191_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r191=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds := by rfl
theorem a_profile191_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a191=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a191.bounds := by rfl
theorem r_fixed191_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 7 := by decide +kernel
theorem a_fixed191_linked : ReferenceProfileData.CoarseLowerShape.Batch0023.a191.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0023.a191.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 9 := by decide +kernel
theorem ranks191_linked : ReferenceRankData.CoarseLowerShape.Batch0023.targetR191=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0023.targetA191=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 1 := by decide +kernel
theorem r_input191_linked : ReferenceRankData.CoarseLowerShape.Batch0023.r191.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds.gauge] := by decide +kernel
theorem a_input191_linked : ReferenceRankData.CoarseLowerShape.Batch0023.a191.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0023.a191.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0023.a191.bounds.gauge] := by decide +kernel
theorem geometry191_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.a := by decide +kernel
theorem weights382_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0047.cert382.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights383_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0047.cert383.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time191_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 10)=true := by decide +kernel
theorem r_reference191_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 0)=true := by decide +kernel
theorem a_reference191_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 1)=true := by decide +kernel
theorem rank_r_link191_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r191 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link191_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0023.a191.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a191 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints191 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell true ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds ReferenceRankData.CoarseLowerShape.Batch0023.r191 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile191_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link191_checked
    geometry191_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell false ReferenceProfileData.CoarseLowerShape.Batch0023.a191.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a191 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile191_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0023.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0023.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link191_checked
    geometry191_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks191_linked.1,←ranks191_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0023.r191.bounds ReferenceRankData.CoarseLowerShape.Batch0023.a191.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0023.ordered191_checked hr ha ho
theorem frozen_frame191 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191 ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds ReferenceProfileData.CoarseLowerShape.Batch0023.a191.bounds
  · rw [←r_profile191_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile191_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry191_linked.2.2.2.2.1
  · exact geometry191_linked.2.2.2.2.2
  · exact r_reference191_checked
  · exact a_reference191_checked
  · exact r_fixed191_linked
  · exact a_fixed191_linked
  · exact time191_checked
  · exact ht
  · exact hw
theorem child_geometry191_checked : ReferenceWeightData.CoarseLowerShape.Batch0047.cert382.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0047.cert382.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0047.cert383.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0047.cert383.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights191 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0047.cert382∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch47_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0047.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0047.cert383∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch47_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0047.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0047.cert382.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0047.cert382.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0047.cert382.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry191_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights382_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0047.cert383.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0047.cert383.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry191_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry191_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights383_linked j (List.mem_finRange j))
theorem actual_frozen_frame191 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame191 (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.flow.timeParameter_mem child_geometry191_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights191 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell184),(ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell185),(ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell186),(ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell187),(ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell188),(ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell189),(ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell190),(ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0023.cell191)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0023.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0023.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame184 hz
  · exact fun z hz=>actual_frozen_frame185 hz
  · exact fun z hz=>actual_frozen_frame186 hz
  · exact fun z hz=>actual_frozen_frame187 hz
  · exact fun z hz=>actual_frozen_frame188 hz
  · exact fun z hz=>actual_frozen_frame189 hz
  · exact fun z hz=>actual_frozen_frame190 hz
  · exact fun z hz=>actual_frozen_frame191 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints184 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints185 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints186 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints187 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints188 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints189 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints190 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints191 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry184_linked.1,geometry184_linked.2.1,geometry184_linked.2.2.1,geometry184_linked.2.2.2.1⟩
  · exact ⟨geometry185_linked.1,geometry185_linked.2.1,geometry185_linked.2.2.1,geometry185_linked.2.2.2.1⟩
  · exact ⟨geometry186_linked.1,geometry186_linked.2.1,geometry186_linked.2.2.1,geometry186_linked.2.2.2.1⟩
  · exact ⟨geometry187_linked.1,geometry187_linked.2.1,geometry187_linked.2.2.1,geometry187_linked.2.2.2.1⟩
  · exact ⟨geometry188_linked.1,geometry188_linked.2.1,geometry188_linked.2.2.1,geometry188_linked.2.2.2.1⟩
  · exact ⟨geometry189_linked.1,geometry189_linked.2.1,geometry189_linked.2.2.1,geometry189_linked.2.2.2.1⟩
  · exact ⟨geometry190_linked.1,geometry190_linked.2.1,geometry190_linked.2.2.1,geometry190_linked.2.2.2.1⟩
  · exact ⟨geometry191_linked.1,geometry191_linked.2.1,geometry191_linked.2.2.1,geometry191_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.a184.bounds,?_,geometry184_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a184.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile184_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds,?_,geometry184_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert184.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r184.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile184_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.a185.bounds,?_,geometry185_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a185.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile185_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds,?_,geometry185_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert185.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r185.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile185_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.a186.bounds,?_,geometry186_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a186.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile186_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds,?_,geometry186_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert186.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r186.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile186_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.a187.bounds,?_,geometry187_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a187.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile187_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds,?_,geometry187_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert187.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r187.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile187_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.a188.bounds,?_,geometry188_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a188.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile188_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds,?_,geometry188_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert188.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r188.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile188_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.a189.bounds,?_,geometry189_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a189.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile189_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds,?_,geometry189_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert189.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r189.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile189_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.a190.bounds,?_,geometry190_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a190.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile190_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds,?_,geometry190_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert190.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r190.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile190_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.a191.bounds,?_,geometry191_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0023.a191.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile191_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds,?_,geometry191_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0023.cert191.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0023.r191.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile191_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0023.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0023.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0023
