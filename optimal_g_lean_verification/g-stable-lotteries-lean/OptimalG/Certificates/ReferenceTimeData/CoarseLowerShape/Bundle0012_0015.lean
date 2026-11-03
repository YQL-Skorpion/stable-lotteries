import OptimalG.Certificates.ReferenceSupportGeometry
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceBranchGeometry
import OptimalG.Certificates.ReferenceTimeBounds
import OptimalG.Certificates.ReferenceFrozenProfiles
import OptimalG.Certificates.ReferenceHessianFrame
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0009_0012
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0009_0012
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0025_0028
import OptimalG.Certificates.ReferenceAdjointData.CoarseLowerShape
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Batch0012
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0011_0014
import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Bundle0008_0011
import OptimalG.Certificates.ReferenceProfileData.CoarseLowerShape.Bundle0013_0016
import OptimalG.Certificates.ReferenceRankData.CoarseLowerShape.Bundle0013_0016
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Batch0013
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0029_0032
import OptimalG.Certificates.ReferenceSensitivityData.CoarseLowerShape.Bundle0014_0017
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0015_0018

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0012
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch24_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0024.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0024.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch25_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0025.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0025.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile96_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r96=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds := by rfl
theorem a_profile96_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a96=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a96.bounds := by rfl
theorem r_fixed96_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 7 := by decide +kernel
theorem a_fixed96_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a96.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.a96.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 9 := by decide +kernel
theorem ranks96_linked : ReferenceRankData.CoarseLowerShape.Batch0012.targetR96=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0012.targetA96=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 1 := by decide +kernel
theorem r_input96_linked : ReferenceRankData.CoarseLowerShape.Batch0012.r96.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds.gauge] := by decide +kernel
theorem a_input96_linked : ReferenceRankData.CoarseLowerShape.Batch0012.a96.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.a96.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.a96.bounds.gauge] := by decide +kernel
theorem geometry96_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.a := by decide +kernel
theorem weights192_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0024.cert192.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights193_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0024.cert193.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time96_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 10)=true := by decide +kernel
theorem r_reference96_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 0)=true := by decide +kernel
theorem a_reference96_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 1)=true := by decide +kernel
theorem rank_r_link96_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r96 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link96_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0012.a96.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a96 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints96 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell true ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r96 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile96_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link96_checked
    geometry96_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell false ReferenceProfileData.CoarseLowerShape.Batch0012.a96.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a96 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile96_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link96_checked
    geometry96_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks96_linked.1,←ranks96_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0012.r96.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a96.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0012.ordered96_checked hr ha ho
theorem frozen_frame96 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96 ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds ReferenceProfileData.CoarseLowerShape.Batch0012.a96.bounds
  · rw [←r_profile96_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile96_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry96_linked.2.2.2.2.1
  · exact geometry96_linked.2.2.2.2.2
  · exact r_reference96_checked
  · exact a_reference96_checked
  · exact r_fixed96_linked
  · exact a_fixed96_linked
  · exact time96_checked
  · exact ht
  · exact hw
theorem child_geometry96_checked : ReferenceWeightData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights96 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0024.cert192∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch24_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0024.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0024.cert193∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch24_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0024.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0024.cert192.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry96_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights192_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0024.cert193.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry96_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry96_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights193_linked j (List.mem_finRange j))
theorem actual_frozen_frame96 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame96 (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.flow.timeParameter_mem child_geometry96_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights96 hz)
theorem r_profile97_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r97=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds := by rfl
theorem a_profile97_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a97=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a97.bounds := by rfl
theorem r_fixed97_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 7 := by decide +kernel
theorem a_fixed97_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a97.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.a97.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 9 := by decide +kernel
theorem ranks97_linked : ReferenceRankData.CoarseLowerShape.Batch0012.targetR97=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0012.targetA97=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 1 := by decide +kernel
theorem r_input97_linked : ReferenceRankData.CoarseLowerShape.Batch0012.r97.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds.gauge] := by decide +kernel
theorem a_input97_linked : ReferenceRankData.CoarseLowerShape.Batch0012.a97.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.a97.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.a97.bounds.gauge] := by decide +kernel
theorem geometry97_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.a := by decide +kernel
theorem weights194_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0024.cert194.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights195_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0024.cert195.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time97_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 10)=true := by decide +kernel
theorem r_reference97_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 0)=true := by decide +kernel
theorem a_reference97_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 1)=true := by decide +kernel
theorem rank_r_link97_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r97 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link97_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0012.a97.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a97 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints97 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell true ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r97 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile97_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link97_checked
    geometry97_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell false ReferenceProfileData.CoarseLowerShape.Batch0012.a97.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a97 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile97_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link97_checked
    geometry97_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks97_linked.1,←ranks97_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0012.r97.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a97.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0012.ordered97_checked hr ha ho
theorem frozen_frame97 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97 ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds ReferenceProfileData.CoarseLowerShape.Batch0012.a97.bounds
  · rw [←r_profile97_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile97_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry97_linked.2.2.2.2.1
  · exact geometry97_linked.2.2.2.2.2
  · exact r_reference97_checked
  · exact a_reference97_checked
  · exact r_fixed97_linked
  · exact a_fixed97_linked
  · exact time97_checked
  · exact ht
  · exact hw
theorem child_geometry97_checked : ReferenceWeightData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights97 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0024.cert194∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch24_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0024.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0024.cert195∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch24_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0024.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0024.cert194.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry97_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights194_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0024.cert195.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry97_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry97_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights195_linked j (List.mem_finRange j))
theorem actual_frozen_frame97 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame97 (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.flow.timeParameter_mem child_geometry97_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights97 hz)
theorem r_profile98_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r98=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds := by rfl
theorem a_profile98_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a98=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a98.bounds := by rfl
theorem r_fixed98_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 7 := by decide +kernel
theorem a_fixed98_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a98.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.a98.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 9 := by decide +kernel
theorem ranks98_linked : ReferenceRankData.CoarseLowerShape.Batch0012.targetR98=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0012.targetA98=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 1 := by decide +kernel
theorem r_input98_linked : ReferenceRankData.CoarseLowerShape.Batch0012.r98.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds.gauge] := by decide +kernel
theorem a_input98_linked : ReferenceRankData.CoarseLowerShape.Batch0012.a98.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.a98.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.a98.bounds.gauge] := by decide +kernel
theorem geometry98_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.a := by decide +kernel
theorem weights196_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0024.cert196.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights197_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0024.cert197.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time98_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 10)=true := by decide +kernel
theorem r_reference98_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 0)=true := by decide +kernel
theorem a_reference98_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 1)=true := by decide +kernel
theorem rank_r_link98_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r98 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link98_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0012.a98.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a98 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints98 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell true ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r98 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile98_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link98_checked
    geometry98_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell false ReferenceProfileData.CoarseLowerShape.Batch0012.a98.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a98 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile98_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link98_checked
    geometry98_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks98_linked.1,←ranks98_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0012.r98.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a98.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0012.ordered98_checked hr ha ho
theorem frozen_frame98 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98 ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds ReferenceProfileData.CoarseLowerShape.Batch0012.a98.bounds
  · rw [←r_profile98_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile98_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry98_linked.2.2.2.2.1
  · exact geometry98_linked.2.2.2.2.2
  · exact r_reference98_checked
  · exact a_reference98_checked
  · exact r_fixed98_linked
  · exact a_fixed98_linked
  · exact time98_checked
  · exact ht
  · exact hw
theorem child_geometry98_checked : ReferenceWeightData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights98 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0024.cert196∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch24_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0024.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0024.cert197∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch24_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0024.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0024.cert196.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry98_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights196_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0024.cert197.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry98_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry98_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights197_linked j (List.mem_finRange j))
theorem actual_frozen_frame98 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame98 (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.flow.timeParameter_mem child_geometry98_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights98 hz)
theorem r_profile99_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r99=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds := by rfl
theorem a_profile99_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a99=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a99.bounds := by rfl
theorem r_fixed99_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 7 := by decide +kernel
theorem a_fixed99_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a99.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.a99.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 9 := by decide +kernel
theorem ranks99_linked : ReferenceRankData.CoarseLowerShape.Batch0012.targetR99=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0012.targetA99=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 1 := by decide +kernel
theorem r_input99_linked : ReferenceRankData.CoarseLowerShape.Batch0012.r99.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds.gauge] := by decide +kernel
theorem a_input99_linked : ReferenceRankData.CoarseLowerShape.Batch0012.a99.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.a99.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.a99.bounds.gauge] := by decide +kernel
theorem geometry99_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.a := by decide +kernel
theorem weights198_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0024.cert198.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights199_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0024.cert199.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time99_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 10)=true := by decide +kernel
theorem r_reference99_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 0)=true := by decide +kernel
theorem a_reference99_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 1)=true := by decide +kernel
theorem rank_r_link99_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r99 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link99_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0012.a99.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a99 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints99 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell true ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r99 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile99_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link99_checked
    geometry99_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell false ReferenceProfileData.CoarseLowerShape.Batch0012.a99.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a99 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile99_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link99_checked
    geometry99_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks99_linked.1,←ranks99_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0012.r99.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a99.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0012.ordered99_checked hr ha ho
theorem frozen_frame99 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99 ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds ReferenceProfileData.CoarseLowerShape.Batch0012.a99.bounds
  · rw [←r_profile99_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile99_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry99_linked.2.2.2.2.1
  · exact geometry99_linked.2.2.2.2.2
  · exact r_reference99_checked
  · exact a_reference99_checked
  · exact r_fixed99_linked
  · exact a_fixed99_linked
  · exact time99_checked
  · exact ht
  · exact hw
theorem child_geometry99_checked : ReferenceWeightData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights99 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0024.cert198∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch24_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0024.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0024.cert199∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch24_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0024.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0024.cert198.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry99_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights198_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0024.cert199.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry99_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry99_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights199_linked j (List.mem_finRange j))
theorem actual_frozen_frame99 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame99 (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.flow.timeParameter_mem child_geometry99_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights99 hz)
theorem r_profile100_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r100=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds := by rfl
theorem a_profile100_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a100=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a100.bounds := by rfl
theorem r_fixed100_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 7 := by decide +kernel
theorem a_fixed100_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a100.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.a100.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 9 := by decide +kernel
theorem ranks100_linked : ReferenceRankData.CoarseLowerShape.Batch0012.targetR100=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0012.targetA100=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 1 := by decide +kernel
theorem r_input100_linked : ReferenceRankData.CoarseLowerShape.Batch0012.r100.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds.gauge] := by decide +kernel
theorem a_input100_linked : ReferenceRankData.CoarseLowerShape.Batch0012.a100.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.a100.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.a100.bounds.gauge] := by decide +kernel
theorem geometry100_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.a := by decide +kernel
theorem weights200_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0025.cert200.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights201_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0025.cert201.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time100_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 10)=true := by decide +kernel
theorem r_reference100_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 0)=true := by decide +kernel
theorem a_reference100_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 1)=true := by decide +kernel
theorem rank_r_link100_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r100 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link100_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0012.a100.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a100 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints100 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell true ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r100 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile100_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link100_checked
    geometry100_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell false ReferenceProfileData.CoarseLowerShape.Batch0012.a100.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a100 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile100_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link100_checked
    geometry100_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks100_linked.1,←ranks100_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0012.r100.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a100.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0012.ordered100_checked hr ha ho
theorem frozen_frame100 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100 ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds ReferenceProfileData.CoarseLowerShape.Batch0012.a100.bounds
  · rw [←r_profile100_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile100_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry100_linked.2.2.2.2.1
  · exact geometry100_linked.2.2.2.2.2
  · exact r_reference100_checked
  · exact a_reference100_checked
  · exact r_fixed100_linked
  · exact a_fixed100_linked
  · exact time100_checked
  · exact ht
  · exact hw
theorem child_geometry100_checked : ReferenceWeightData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights100 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0025.cert200∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch25_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0025.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0025.cert201∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch25_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0025.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0025.cert200.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry100_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights200_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0025.cert201.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry100_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry100_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights201_linked j (List.mem_finRange j))
theorem actual_frozen_frame100 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame100 (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.flow.timeParameter_mem child_geometry100_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights100 hz)
theorem r_profile101_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r101=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds := by rfl
theorem a_profile101_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a101=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a101.bounds := by rfl
theorem r_fixed101_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 7 := by decide +kernel
theorem a_fixed101_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a101.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.a101.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 9 := by decide +kernel
theorem ranks101_linked : ReferenceRankData.CoarseLowerShape.Batch0012.targetR101=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0012.targetA101=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 1 := by decide +kernel
theorem r_input101_linked : ReferenceRankData.CoarseLowerShape.Batch0012.r101.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds.gauge] := by decide +kernel
theorem a_input101_linked : ReferenceRankData.CoarseLowerShape.Batch0012.a101.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.a101.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.a101.bounds.gauge] := by decide +kernel
theorem geometry101_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.a := by decide +kernel
theorem weights202_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0025.cert202.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights203_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0025.cert203.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time101_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 10)=true := by decide +kernel
theorem r_reference101_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 0)=true := by decide +kernel
theorem a_reference101_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 1)=true := by decide +kernel
theorem rank_r_link101_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r101 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link101_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0012.a101.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a101 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints101 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell true ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r101 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile101_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link101_checked
    geometry101_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell false ReferenceProfileData.CoarseLowerShape.Batch0012.a101.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a101 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile101_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link101_checked
    geometry101_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks101_linked.1,←ranks101_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0012.r101.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a101.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0012.ordered101_checked hr ha ho
theorem frozen_frame101 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101 ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds ReferenceProfileData.CoarseLowerShape.Batch0012.a101.bounds
  · rw [←r_profile101_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile101_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry101_linked.2.2.2.2.1
  · exact geometry101_linked.2.2.2.2.2
  · exact r_reference101_checked
  · exact a_reference101_checked
  · exact r_fixed101_linked
  · exact a_fixed101_linked
  · exact time101_checked
  · exact ht
  · exact hw
theorem child_geometry101_checked : ReferenceWeightData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights101 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0025.cert202∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch25_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0025.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0025.cert203∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch25_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0025.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0025.cert202.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry101_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights202_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0025.cert203.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry101_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry101_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights203_linked j (List.mem_finRange j))
theorem actual_frozen_frame101 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame101 (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.flow.timeParameter_mem child_geometry101_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights101 hz)
theorem r_profile102_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r102=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds := by rfl
theorem a_profile102_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a102=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a102.bounds := by rfl
theorem r_fixed102_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 7 := by decide +kernel
theorem a_fixed102_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a102.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.a102.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 9 := by decide +kernel
theorem ranks102_linked : ReferenceRankData.CoarseLowerShape.Batch0012.targetR102=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0012.targetA102=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 1 := by decide +kernel
theorem r_input102_linked : ReferenceRankData.CoarseLowerShape.Batch0012.r102.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds.gauge] := by decide +kernel
theorem a_input102_linked : ReferenceRankData.CoarseLowerShape.Batch0012.a102.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.a102.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.a102.bounds.gauge] := by decide +kernel
theorem geometry102_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.a := by decide +kernel
theorem weights204_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0025.cert204.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights205_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0025.cert205.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time102_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 10)=true := by decide +kernel
theorem r_reference102_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 0)=true := by decide +kernel
theorem a_reference102_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 1)=true := by decide +kernel
theorem rank_r_link102_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r102 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link102_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0012.a102.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a102 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints102 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell true ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r102 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile102_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link102_checked
    geometry102_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell false ReferenceProfileData.CoarseLowerShape.Batch0012.a102.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a102 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile102_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link102_checked
    geometry102_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks102_linked.1,←ranks102_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0012.r102.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a102.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0012.ordered102_checked hr ha ho
theorem frozen_frame102 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102 ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds ReferenceProfileData.CoarseLowerShape.Batch0012.a102.bounds
  · rw [←r_profile102_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile102_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry102_linked.2.2.2.2.1
  · exact geometry102_linked.2.2.2.2.2
  · exact r_reference102_checked
  · exact a_reference102_checked
  · exact r_fixed102_linked
  · exact a_fixed102_linked
  · exact time102_checked
  · exact ht
  · exact hw
theorem child_geometry102_checked : ReferenceWeightData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights102 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0025.cert204∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch25_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0025.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0025.cert205∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch25_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0025.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0025.cert204.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry102_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights204_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0025.cert205.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry102_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry102_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights205_linked j (List.mem_finRange j))
theorem actual_frozen_frame102 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame102 (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.flow.timeParameter_mem child_geometry102_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights102 hz)
theorem r_profile103_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r103=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds := by rfl
theorem a_profile103_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a103=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a103.bounds := by rfl
theorem r_fixed103_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 7 := by decide +kernel
theorem a_fixed103_linked : ReferenceProfileData.CoarseLowerShape.Batch0012.a103.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0012.a103.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 9 := by decide +kernel
theorem ranks103_linked : ReferenceRankData.CoarseLowerShape.Batch0012.targetR103=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0012.targetA103=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 1 := by decide +kernel
theorem r_input103_linked : ReferenceRankData.CoarseLowerShape.Batch0012.r103.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds.gauge] := by decide +kernel
theorem a_input103_linked : ReferenceRankData.CoarseLowerShape.Batch0012.a103.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0012.a103.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0012.a103.bounds.gauge] := by decide +kernel
theorem geometry103_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.a := by decide +kernel
theorem weights206_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0025.cert206.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights207_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0025.cert207.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time103_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 10)=true := by decide +kernel
theorem r_reference103_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 0)=true := by decide +kernel
theorem a_reference103_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 1)=true := by decide +kernel
theorem rank_r_link103_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r103 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link103_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0012.a103.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a103 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints103 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell true ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds ReferenceRankData.CoarseLowerShape.Batch0012.r103 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile103_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link103_checked
    geometry103_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell false ReferenceProfileData.CoarseLowerShape.Batch0012.a103.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a103 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile103_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0012.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0012.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link103_checked
    geometry103_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks103_linked.1,←ranks103_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0012.r103.bounds ReferenceRankData.CoarseLowerShape.Batch0012.a103.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0012.ordered103_checked hr ha ho
theorem frozen_frame103 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103 ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds ReferenceProfileData.CoarseLowerShape.Batch0012.a103.bounds
  · rw [←r_profile103_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile103_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry103_linked.2.2.2.2.1
  · exact geometry103_linked.2.2.2.2.2
  · exact r_reference103_checked
  · exact a_reference103_checked
  · exact r_fixed103_linked
  · exact a_fixed103_linked
  · exact time103_checked
  · exact ht
  · exact hw
theorem child_geometry103_checked : ReferenceWeightData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights103 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0025.cert206∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch25_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0025.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0025.cert207∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch25_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0025.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0025.cert206.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry103_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights206_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0025.cert207.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry103_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry103_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights207_linked j (List.mem_finRange j))
theorem actual_frozen_frame103 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame103 (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.flow.timeParameter_mem child_geometry103_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights103 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell96),(ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell97),(ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell98),(ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell99),(ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell100),(ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell101),(ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell102),(ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0012.cell103)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0012.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0012.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame96 hz
  · exact fun z hz=>actual_frozen_frame97 hz
  · exact fun z hz=>actual_frozen_frame98 hz
  · exact fun z hz=>actual_frozen_frame99 hz
  · exact fun z hz=>actual_frozen_frame100 hz
  · exact fun z hz=>actual_frozen_frame101 hz
  · exact fun z hz=>actual_frozen_frame102 hz
  · exact fun z hz=>actual_frozen_frame103 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints96 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints97 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints98 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints99 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints100 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints101 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints102 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints103 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry96_linked.1,geometry96_linked.2.1,geometry96_linked.2.2.1,geometry96_linked.2.2.2.1⟩
  · exact ⟨geometry97_linked.1,geometry97_linked.2.1,geometry97_linked.2.2.1,geometry97_linked.2.2.2.1⟩
  · exact ⟨geometry98_linked.1,geometry98_linked.2.1,geometry98_linked.2.2.1,geometry98_linked.2.2.2.1⟩
  · exact ⟨geometry99_linked.1,geometry99_linked.2.1,geometry99_linked.2.2.1,geometry99_linked.2.2.2.1⟩
  · exact ⟨geometry100_linked.1,geometry100_linked.2.1,geometry100_linked.2.2.1,geometry100_linked.2.2.2.1⟩
  · exact ⟨geometry101_linked.1,geometry101_linked.2.1,geometry101_linked.2.2.1,geometry101_linked.2.2.2.1⟩
  · exact ⟨geometry102_linked.1,geometry102_linked.2.1,geometry102_linked.2.2.1,geometry102_linked.2.2.2.1⟩
  · exact ⟨geometry103_linked.1,geometry103_linked.2.1,geometry103_linked.2.2.1,geometry103_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.a96.bounds,?_,geometry96_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a96.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile96_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds,?_,geometry96_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert96.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r96.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile96_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.a97.bounds,?_,geometry97_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a97.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile97_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds,?_,geometry97_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert97.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r97.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile97_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.a98.bounds,?_,geometry98_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a98.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile98_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds,?_,geometry98_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert98.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r98.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile98_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.a99.bounds,?_,geometry99_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a99.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile99_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds,?_,geometry99_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert99.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r99.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile99_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.a100.bounds,?_,geometry100_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a100.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile100_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds,?_,geometry100_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert100.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r100.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile100_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.a101.bounds,?_,geometry101_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a101.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile101_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds,?_,geometry101_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert101.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r101.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile101_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.a102.bounds,?_,geometry102_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a102.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile102_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds,?_,geometry102_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert102.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r102.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile102_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.a103.bounds,?_,geometry103_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0012.a103.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile103_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds,?_,geometry103_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0012.cert103.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0012.r103.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile103_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0012.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0012.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0012

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0013
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch26_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0026.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0026.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch27_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0027.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0027.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile104_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r104=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds := by rfl
theorem a_profile104_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a104=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a104.bounds := by rfl
theorem r_fixed104_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 7 := by decide +kernel
theorem a_fixed104_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a104.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.a104.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 9 := by decide +kernel
theorem ranks104_linked : ReferenceRankData.CoarseLowerShape.Batch0013.targetR104=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0013.targetA104=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 1 := by decide +kernel
theorem r_input104_linked : ReferenceRankData.CoarseLowerShape.Batch0013.r104.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds.gauge] := by decide +kernel
theorem a_input104_linked : ReferenceRankData.CoarseLowerShape.Batch0013.a104.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.a104.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.a104.bounds.gauge] := by decide +kernel
theorem geometry104_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.a := by decide +kernel
theorem weights208_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0026.cert208.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights209_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0026.cert209.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time104_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 10)=true := by decide +kernel
theorem r_reference104_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 0)=true := by decide +kernel
theorem a_reference104_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 1)=true := by decide +kernel
theorem rank_r_link104_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r104 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link104_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0013.a104.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a104 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints104 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell true ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r104 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile104_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link104_checked
    geometry104_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell false ReferenceProfileData.CoarseLowerShape.Batch0013.a104.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a104 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile104_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link104_checked
    geometry104_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks104_linked.1,←ranks104_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0013.r104.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a104.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0013.ordered104_checked hr ha ho
theorem frozen_frame104 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104 ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds ReferenceProfileData.CoarseLowerShape.Batch0013.a104.bounds
  · rw [←r_profile104_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile104_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry104_linked.2.2.2.2.1
  · exact geometry104_linked.2.2.2.2.2
  · exact r_reference104_checked
  · exact a_reference104_checked
  · exact r_fixed104_linked
  · exact a_fixed104_linked
  · exact time104_checked
  · exact ht
  · exact hw
theorem child_geometry104_checked : ReferenceWeightData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights104 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0026.cert208∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch26_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0026.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0026.cert209∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch26_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0026.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0026.cert208.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry104_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights208_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0026.cert209.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry104_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry104_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights209_linked j (List.mem_finRange j))
theorem actual_frozen_frame104 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame104 (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.flow.timeParameter_mem child_geometry104_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights104 hz)
theorem r_profile105_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r105=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds := by rfl
theorem a_profile105_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a105=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a105.bounds := by rfl
theorem r_fixed105_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 7 := by decide +kernel
theorem a_fixed105_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a105.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.a105.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 9 := by decide +kernel
theorem ranks105_linked : ReferenceRankData.CoarseLowerShape.Batch0013.targetR105=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0013.targetA105=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 1 := by decide +kernel
theorem r_input105_linked : ReferenceRankData.CoarseLowerShape.Batch0013.r105.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds.gauge] := by decide +kernel
theorem a_input105_linked : ReferenceRankData.CoarseLowerShape.Batch0013.a105.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.a105.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.a105.bounds.gauge] := by decide +kernel
theorem geometry105_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.a := by decide +kernel
theorem weights210_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0026.cert210.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights211_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0026.cert211.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time105_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 10)=true := by decide +kernel
theorem r_reference105_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 0)=true := by decide +kernel
theorem a_reference105_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 1)=true := by decide +kernel
theorem rank_r_link105_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r105 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link105_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0013.a105.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a105 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints105 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell true ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r105 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile105_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link105_checked
    geometry105_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell false ReferenceProfileData.CoarseLowerShape.Batch0013.a105.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a105 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile105_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link105_checked
    geometry105_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks105_linked.1,←ranks105_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0013.r105.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a105.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0013.ordered105_checked hr ha ho
theorem frozen_frame105 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105 ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds ReferenceProfileData.CoarseLowerShape.Batch0013.a105.bounds
  · rw [←r_profile105_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile105_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry105_linked.2.2.2.2.1
  · exact geometry105_linked.2.2.2.2.2
  · exact r_reference105_checked
  · exact a_reference105_checked
  · exact r_fixed105_linked
  · exact a_fixed105_linked
  · exact time105_checked
  · exact ht
  · exact hw
theorem child_geometry105_checked : ReferenceWeightData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights105 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0026.cert210∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch26_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0026.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0026.cert211∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch26_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0026.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0026.cert210.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry105_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights210_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0026.cert211.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry105_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry105_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights211_linked j (List.mem_finRange j))
theorem actual_frozen_frame105 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame105 (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.flow.timeParameter_mem child_geometry105_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights105 hz)
theorem r_profile106_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r106=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds := by rfl
theorem a_profile106_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a106=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a106.bounds := by rfl
theorem r_fixed106_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 7 := by decide +kernel
theorem a_fixed106_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a106.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.a106.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 9 := by decide +kernel
theorem ranks106_linked : ReferenceRankData.CoarseLowerShape.Batch0013.targetR106=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0013.targetA106=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 1 := by decide +kernel
theorem r_input106_linked : ReferenceRankData.CoarseLowerShape.Batch0013.r106.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds.gauge] := by decide +kernel
theorem a_input106_linked : ReferenceRankData.CoarseLowerShape.Batch0013.a106.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.a106.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.a106.bounds.gauge] := by decide +kernel
theorem geometry106_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.a := by decide +kernel
theorem weights212_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0026.cert212.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights213_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0026.cert213.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time106_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 10)=true := by decide +kernel
theorem r_reference106_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 0)=true := by decide +kernel
theorem a_reference106_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 1)=true := by decide +kernel
theorem rank_r_link106_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r106 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link106_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0013.a106.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a106 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints106 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell true ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r106 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile106_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link106_checked
    geometry106_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell false ReferenceProfileData.CoarseLowerShape.Batch0013.a106.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a106 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile106_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link106_checked
    geometry106_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks106_linked.1,←ranks106_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0013.r106.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a106.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0013.ordered106_checked hr ha ho
theorem frozen_frame106 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106 ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds ReferenceProfileData.CoarseLowerShape.Batch0013.a106.bounds
  · rw [←r_profile106_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile106_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry106_linked.2.2.2.2.1
  · exact geometry106_linked.2.2.2.2.2
  · exact r_reference106_checked
  · exact a_reference106_checked
  · exact r_fixed106_linked
  · exact a_fixed106_linked
  · exact time106_checked
  · exact ht
  · exact hw
theorem child_geometry106_checked : ReferenceWeightData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights106 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0026.cert212∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch26_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0026.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0026.cert213∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch26_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0026.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0026.cert212.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry106_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights212_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0026.cert213.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry106_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry106_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights213_linked j (List.mem_finRange j))
theorem actual_frozen_frame106 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame106 (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.flow.timeParameter_mem child_geometry106_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights106 hz)
theorem r_profile107_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r107=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds := by rfl
theorem a_profile107_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a107=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a107.bounds := by rfl
theorem r_fixed107_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 7 := by decide +kernel
theorem a_fixed107_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a107.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.a107.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 9 := by decide +kernel
theorem ranks107_linked : ReferenceRankData.CoarseLowerShape.Batch0013.targetR107=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0013.targetA107=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 1 := by decide +kernel
theorem r_input107_linked : ReferenceRankData.CoarseLowerShape.Batch0013.r107.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds.gauge] := by decide +kernel
theorem a_input107_linked : ReferenceRankData.CoarseLowerShape.Batch0013.a107.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.a107.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.a107.bounds.gauge] := by decide +kernel
theorem geometry107_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.a := by decide +kernel
theorem weights214_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0026.cert214.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights215_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0026.cert215.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time107_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 10)=true := by decide +kernel
theorem r_reference107_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 0)=true := by decide +kernel
theorem a_reference107_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 1)=true := by decide +kernel
theorem rank_r_link107_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r107 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link107_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0013.a107.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a107 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints107 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell true ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r107 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile107_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link107_checked
    geometry107_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell false ReferenceProfileData.CoarseLowerShape.Batch0013.a107.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a107 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile107_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link107_checked
    geometry107_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks107_linked.1,←ranks107_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0013.r107.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a107.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0013.ordered107_checked hr ha ho
theorem frozen_frame107 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107 ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds ReferenceProfileData.CoarseLowerShape.Batch0013.a107.bounds
  · rw [←r_profile107_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile107_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry107_linked.2.2.2.2.1
  · exact geometry107_linked.2.2.2.2.2
  · exact r_reference107_checked
  · exact a_reference107_checked
  · exact r_fixed107_linked
  · exact a_fixed107_linked
  · exact time107_checked
  · exact ht
  · exact hw
theorem child_geometry107_checked : ReferenceWeightData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights107 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0026.cert214∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch26_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0026.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0026.cert215∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch26_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0026.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0026.cert214.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry107_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights214_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0026.cert215.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry107_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry107_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights215_linked j (List.mem_finRange j))
theorem actual_frozen_frame107 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame107 (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.flow.timeParameter_mem child_geometry107_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights107 hz)
theorem r_profile108_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r108=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds := by rfl
theorem a_profile108_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a108=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a108.bounds := by rfl
theorem r_fixed108_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 7 := by decide +kernel
theorem a_fixed108_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a108.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.a108.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 9 := by decide +kernel
theorem ranks108_linked : ReferenceRankData.CoarseLowerShape.Batch0013.targetR108=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0013.targetA108=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 1 := by decide +kernel
theorem r_input108_linked : ReferenceRankData.CoarseLowerShape.Batch0013.r108.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds.gauge] := by decide +kernel
theorem a_input108_linked : ReferenceRankData.CoarseLowerShape.Batch0013.a108.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.a108.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.a108.bounds.gauge] := by decide +kernel
theorem geometry108_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.a := by decide +kernel
theorem weights216_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0027.cert216.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights217_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0027.cert217.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time108_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 10)=true := by decide +kernel
theorem r_reference108_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 0)=true := by decide +kernel
theorem a_reference108_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 1)=true := by decide +kernel
theorem rank_r_link108_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r108 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link108_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0013.a108.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a108 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints108 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell true ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r108 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile108_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link108_checked
    geometry108_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell false ReferenceProfileData.CoarseLowerShape.Batch0013.a108.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a108 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile108_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link108_checked
    geometry108_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks108_linked.1,←ranks108_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0013.r108.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a108.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0013.ordered108_checked hr ha ho
theorem frozen_frame108 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108 ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds ReferenceProfileData.CoarseLowerShape.Batch0013.a108.bounds
  · rw [←r_profile108_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile108_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry108_linked.2.2.2.2.1
  · exact geometry108_linked.2.2.2.2.2
  · exact r_reference108_checked
  · exact a_reference108_checked
  · exact r_fixed108_linked
  · exact a_fixed108_linked
  · exact time108_checked
  · exact ht
  · exact hw
theorem child_geometry108_checked : ReferenceWeightData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights108 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0027.cert216∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch27_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0027.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0027.cert217∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch27_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0027.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0027.cert216.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry108_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights216_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0027.cert217.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry108_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry108_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights217_linked j (List.mem_finRange j))
theorem actual_frozen_frame108 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame108 (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.flow.timeParameter_mem child_geometry108_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights108 hz)
theorem r_profile109_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r109=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds := by rfl
theorem a_profile109_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a109=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a109.bounds := by rfl
theorem r_fixed109_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 7 := by decide +kernel
theorem a_fixed109_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a109.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.a109.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 9 := by decide +kernel
theorem ranks109_linked : ReferenceRankData.CoarseLowerShape.Batch0013.targetR109=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0013.targetA109=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 1 := by decide +kernel
theorem r_input109_linked : ReferenceRankData.CoarseLowerShape.Batch0013.r109.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds.gauge] := by decide +kernel
theorem a_input109_linked : ReferenceRankData.CoarseLowerShape.Batch0013.a109.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.a109.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.a109.bounds.gauge] := by decide +kernel
theorem geometry109_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.a := by decide +kernel
theorem weights218_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0027.cert218.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights219_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0027.cert219.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time109_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 10)=true := by decide +kernel
theorem r_reference109_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 0)=true := by decide +kernel
theorem a_reference109_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 1)=true := by decide +kernel
theorem rank_r_link109_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r109 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link109_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0013.a109.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a109 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints109 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell true ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r109 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile109_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link109_checked
    geometry109_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell false ReferenceProfileData.CoarseLowerShape.Batch0013.a109.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a109 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile109_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link109_checked
    geometry109_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks109_linked.1,←ranks109_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0013.r109.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a109.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0013.ordered109_checked hr ha ho
theorem frozen_frame109 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109 ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds ReferenceProfileData.CoarseLowerShape.Batch0013.a109.bounds
  · rw [←r_profile109_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile109_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry109_linked.2.2.2.2.1
  · exact geometry109_linked.2.2.2.2.2
  · exact r_reference109_checked
  · exact a_reference109_checked
  · exact r_fixed109_linked
  · exact a_fixed109_linked
  · exact time109_checked
  · exact ht
  · exact hw
theorem child_geometry109_checked : ReferenceWeightData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights109 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0027.cert218∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch27_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0027.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0027.cert219∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch27_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0027.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0027.cert218.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry109_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights218_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0027.cert219.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry109_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry109_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights219_linked j (List.mem_finRange j))
theorem actual_frozen_frame109 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame109 (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.flow.timeParameter_mem child_geometry109_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights109 hz)
theorem r_profile110_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r110=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds := by rfl
theorem a_profile110_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a110=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a110.bounds := by rfl
theorem r_fixed110_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 7 := by decide +kernel
theorem a_fixed110_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a110.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.a110.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 9 := by decide +kernel
theorem ranks110_linked : ReferenceRankData.CoarseLowerShape.Batch0013.targetR110=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0013.targetA110=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 1 := by decide +kernel
theorem r_input110_linked : ReferenceRankData.CoarseLowerShape.Batch0013.r110.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds.gauge] := by decide +kernel
theorem a_input110_linked : ReferenceRankData.CoarseLowerShape.Batch0013.a110.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.a110.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.a110.bounds.gauge] := by decide +kernel
theorem geometry110_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.a := by decide +kernel
theorem weights220_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0027.cert220.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights221_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0027.cert221.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time110_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 10)=true := by decide +kernel
theorem r_reference110_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 0)=true := by decide +kernel
theorem a_reference110_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 1)=true := by decide +kernel
theorem rank_r_link110_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r110 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link110_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0013.a110.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a110 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints110 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell true ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r110 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile110_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link110_checked
    geometry110_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell false ReferenceProfileData.CoarseLowerShape.Batch0013.a110.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a110 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile110_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link110_checked
    geometry110_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks110_linked.1,←ranks110_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0013.r110.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a110.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0013.ordered110_checked hr ha ho
theorem frozen_frame110 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110 ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds ReferenceProfileData.CoarseLowerShape.Batch0013.a110.bounds
  · rw [←r_profile110_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile110_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry110_linked.2.2.2.2.1
  · exact geometry110_linked.2.2.2.2.2
  · exact r_reference110_checked
  · exact a_reference110_checked
  · exact r_fixed110_linked
  · exact a_fixed110_linked
  · exact time110_checked
  · exact ht
  · exact hw
theorem child_geometry110_checked : ReferenceWeightData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights110 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0027.cert220∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch27_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0027.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0027.cert221∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch27_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0027.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0027.cert220.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry110_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights220_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0027.cert221.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry110_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry110_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights221_linked j (List.mem_finRange j))
theorem actual_frozen_frame110 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame110 (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.flow.timeParameter_mem child_geometry110_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights110 hz)
theorem r_profile111_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r111=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds := by rfl
theorem a_profile111_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a111=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a111.bounds := by rfl
theorem r_fixed111_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 7 := by decide +kernel
theorem a_fixed111_linked : ReferenceProfileData.CoarseLowerShape.Batch0013.a111.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0013.a111.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 9 := by decide +kernel
theorem ranks111_linked : ReferenceRankData.CoarseLowerShape.Batch0013.targetR111=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0013.targetA111=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 1 := by decide +kernel
theorem r_input111_linked : ReferenceRankData.CoarseLowerShape.Batch0013.r111.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds.gauge] := by decide +kernel
theorem a_input111_linked : ReferenceRankData.CoarseLowerShape.Batch0013.a111.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0013.a111.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0013.a111.bounds.gauge] := by decide +kernel
theorem geometry111_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.a := by decide +kernel
theorem weights222_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0027.cert222.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights223_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0027.cert223.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time111_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 10)=true := by decide +kernel
theorem r_reference111_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 0)=true := by decide +kernel
theorem a_reference111_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 1)=true := by decide +kernel
theorem rank_r_link111_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r111 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link111_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0013.a111.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a111 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints111 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell true ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds ReferenceRankData.CoarseLowerShape.Batch0013.r111 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile111_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link111_checked
    geometry111_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell false ReferenceProfileData.CoarseLowerShape.Batch0013.a111.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a111 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile111_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0013.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0013.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link111_checked
    geometry111_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks111_linked.1,←ranks111_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0013.r111.bounds ReferenceRankData.CoarseLowerShape.Batch0013.a111.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0013.ordered111_checked hr ha ho
theorem frozen_frame111 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111 ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds ReferenceProfileData.CoarseLowerShape.Batch0013.a111.bounds
  · rw [←r_profile111_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile111_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry111_linked.2.2.2.2.1
  · exact geometry111_linked.2.2.2.2.2
  · exact r_reference111_checked
  · exact a_reference111_checked
  · exact r_fixed111_linked
  · exact a_fixed111_linked
  · exact time111_checked
  · exact ht
  · exact hw
theorem child_geometry111_checked : ReferenceWeightData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights111 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0027.cert222∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch27_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0027.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0027.cert223∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch27_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0027.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0027.cert222.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry111_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights222_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0027.cert223.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry111_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry111_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights223_linked j (List.mem_finRange j))
theorem actual_frozen_frame111 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame111 (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.flow.timeParameter_mem child_geometry111_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights111 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell104),(ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell105),(ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell106),(ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell107),(ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell108),(ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell109),(ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell110),(ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0013.cell111)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0013.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0013.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame104 hz
  · exact fun z hz=>actual_frozen_frame105 hz
  · exact fun z hz=>actual_frozen_frame106 hz
  · exact fun z hz=>actual_frozen_frame107 hz
  · exact fun z hz=>actual_frozen_frame108 hz
  · exact fun z hz=>actual_frozen_frame109 hz
  · exact fun z hz=>actual_frozen_frame110 hz
  · exact fun z hz=>actual_frozen_frame111 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints104 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints105 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints106 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints107 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints108 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints109 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints110 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints111 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry104_linked.1,geometry104_linked.2.1,geometry104_linked.2.2.1,geometry104_linked.2.2.2.1⟩
  · exact ⟨geometry105_linked.1,geometry105_linked.2.1,geometry105_linked.2.2.1,geometry105_linked.2.2.2.1⟩
  · exact ⟨geometry106_linked.1,geometry106_linked.2.1,geometry106_linked.2.2.1,geometry106_linked.2.2.2.1⟩
  · exact ⟨geometry107_linked.1,geometry107_linked.2.1,geometry107_linked.2.2.1,geometry107_linked.2.2.2.1⟩
  · exact ⟨geometry108_linked.1,geometry108_linked.2.1,geometry108_linked.2.2.1,geometry108_linked.2.2.2.1⟩
  · exact ⟨geometry109_linked.1,geometry109_linked.2.1,geometry109_linked.2.2.1,geometry109_linked.2.2.2.1⟩
  · exact ⟨geometry110_linked.1,geometry110_linked.2.1,geometry110_linked.2.2.1,geometry110_linked.2.2.2.1⟩
  · exact ⟨geometry111_linked.1,geometry111_linked.2.1,geometry111_linked.2.2.1,geometry111_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.a104.bounds,?_,geometry104_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a104.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile104_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds,?_,geometry104_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert104.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r104.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile104_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.a105.bounds,?_,geometry105_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a105.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile105_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds,?_,geometry105_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert105.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r105.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile105_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.a106.bounds,?_,geometry106_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a106.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile106_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds,?_,geometry106_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert106.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r106.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile106_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.a107.bounds,?_,geometry107_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a107.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile107_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds,?_,geometry107_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert107.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r107.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile107_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.a108.bounds,?_,geometry108_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a108.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile108_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds,?_,geometry108_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert108.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r108.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile108_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.a109.bounds,?_,geometry109_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a109.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile109_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds,?_,geometry109_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert109.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r109.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile109_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.a110.bounds,?_,geometry110_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a110.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile110_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds,?_,geometry110_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert110.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r110.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile110_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.a111.bounds,?_,geometry111_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0013.a111.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile111_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds,?_,geometry111_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0013.cert111.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0013.r111.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile111_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0013.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0013.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0013

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0014
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch28_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0028.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0028.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch29_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0029.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0029.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile112_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r112=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds := by rfl
theorem a_profile112_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a112=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a112.bounds := by rfl
theorem r_fixed112_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 7 := by decide +kernel
theorem a_fixed112_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a112.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.a112.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 9 := by decide +kernel
theorem ranks112_linked : ReferenceRankData.CoarseLowerShape.Batch0014.targetR112=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0014.targetA112=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 1 := by decide +kernel
theorem r_input112_linked : ReferenceRankData.CoarseLowerShape.Batch0014.r112.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds.gauge] := by decide +kernel
theorem a_input112_linked : ReferenceRankData.CoarseLowerShape.Batch0014.a112.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.a112.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.a112.bounds.gauge] := by decide +kernel
theorem geometry112_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.a := by decide +kernel
theorem weights224_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0028.cert224.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights225_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0028.cert225.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time112_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 10)=true := by decide +kernel
theorem r_reference112_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 0)=true := by decide +kernel
theorem a_reference112_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 1)=true := by decide +kernel
theorem rank_r_link112_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r112 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link112_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0014.a112.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a112 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints112 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell true ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r112 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile112_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link112_checked
    geometry112_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell false ReferenceProfileData.CoarseLowerShape.Batch0014.a112.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a112 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile112_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link112_checked
    geometry112_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks112_linked.1,←ranks112_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0014.r112.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a112.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0014.ordered112_checked hr ha ho
theorem frozen_frame112 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112 ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds ReferenceProfileData.CoarseLowerShape.Batch0014.a112.bounds
  · rw [←r_profile112_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile112_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry112_linked.2.2.2.2.1
  · exact geometry112_linked.2.2.2.2.2
  · exact r_reference112_checked
  · exact a_reference112_checked
  · exact r_fixed112_linked
  · exact a_fixed112_linked
  · exact time112_checked
  · exact ht
  · exact hw
theorem child_geometry112_checked : ReferenceWeightData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights112 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0028.cert224∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch28_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0028.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0028.cert225∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch28_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0028.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0028.cert224.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry112_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights224_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0028.cert225.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry112_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry112_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights225_linked j (List.mem_finRange j))
theorem actual_frozen_frame112 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame112 (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.flow.timeParameter_mem child_geometry112_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights112 hz)
theorem r_profile113_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r113=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds := by rfl
theorem a_profile113_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a113=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a113.bounds := by rfl
theorem r_fixed113_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 7 := by decide +kernel
theorem a_fixed113_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a113.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.a113.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 9 := by decide +kernel
theorem ranks113_linked : ReferenceRankData.CoarseLowerShape.Batch0014.targetR113=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0014.targetA113=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 1 := by decide +kernel
theorem r_input113_linked : ReferenceRankData.CoarseLowerShape.Batch0014.r113.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds.gauge] := by decide +kernel
theorem a_input113_linked : ReferenceRankData.CoarseLowerShape.Batch0014.a113.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.a113.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.a113.bounds.gauge] := by decide +kernel
theorem geometry113_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.a := by decide +kernel
theorem weights226_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0028.cert226.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights227_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0028.cert227.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time113_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 10)=true := by decide +kernel
theorem r_reference113_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 0)=true := by decide +kernel
theorem a_reference113_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 1)=true := by decide +kernel
theorem rank_r_link113_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r113 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link113_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0014.a113.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a113 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints113 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell true ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r113 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile113_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link113_checked
    geometry113_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell false ReferenceProfileData.CoarseLowerShape.Batch0014.a113.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a113 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile113_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link113_checked
    geometry113_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks113_linked.1,←ranks113_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0014.r113.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a113.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0014.ordered113_checked hr ha ho
theorem frozen_frame113 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113 ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds ReferenceProfileData.CoarseLowerShape.Batch0014.a113.bounds
  · rw [←r_profile113_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile113_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry113_linked.2.2.2.2.1
  · exact geometry113_linked.2.2.2.2.2
  · exact r_reference113_checked
  · exact a_reference113_checked
  · exact r_fixed113_linked
  · exact a_fixed113_linked
  · exact time113_checked
  · exact ht
  · exact hw
theorem child_geometry113_checked : ReferenceWeightData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights113 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0028.cert226∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch28_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0028.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0028.cert227∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch28_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0028.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0028.cert226.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry113_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights226_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0028.cert227.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry113_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry113_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights227_linked j (List.mem_finRange j))
theorem actual_frozen_frame113 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame113 (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.flow.timeParameter_mem child_geometry113_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights113 hz)
theorem r_profile114_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r114=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds := by rfl
theorem a_profile114_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a114=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a114.bounds := by rfl
theorem r_fixed114_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 7 := by decide +kernel
theorem a_fixed114_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a114.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.a114.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 9 := by decide +kernel
theorem ranks114_linked : ReferenceRankData.CoarseLowerShape.Batch0014.targetR114=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0014.targetA114=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 1 := by decide +kernel
theorem r_input114_linked : ReferenceRankData.CoarseLowerShape.Batch0014.r114.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds.gauge] := by decide +kernel
theorem a_input114_linked : ReferenceRankData.CoarseLowerShape.Batch0014.a114.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.a114.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.a114.bounds.gauge] := by decide +kernel
theorem geometry114_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.a := by decide +kernel
theorem weights228_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0028.cert228.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights229_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0028.cert229.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time114_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 10)=true := by decide +kernel
theorem r_reference114_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 0)=true := by decide +kernel
theorem a_reference114_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 1)=true := by decide +kernel
theorem rank_r_link114_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r114 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link114_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0014.a114.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a114 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints114 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell true ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r114 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile114_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link114_checked
    geometry114_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell false ReferenceProfileData.CoarseLowerShape.Batch0014.a114.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a114 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile114_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link114_checked
    geometry114_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks114_linked.1,←ranks114_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0014.r114.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a114.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0014.ordered114_checked hr ha ho
theorem frozen_frame114 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114 ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds ReferenceProfileData.CoarseLowerShape.Batch0014.a114.bounds
  · rw [←r_profile114_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile114_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry114_linked.2.2.2.2.1
  · exact geometry114_linked.2.2.2.2.2
  · exact r_reference114_checked
  · exact a_reference114_checked
  · exact r_fixed114_linked
  · exact a_fixed114_linked
  · exact time114_checked
  · exact ht
  · exact hw
theorem child_geometry114_checked : ReferenceWeightData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights114 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0028.cert228∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch28_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0028.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0028.cert229∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch28_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0028.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0028.cert228.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry114_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights228_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0028.cert229.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry114_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry114_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights229_linked j (List.mem_finRange j))
theorem actual_frozen_frame114 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame114 (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.flow.timeParameter_mem child_geometry114_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights114 hz)
theorem r_profile115_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r115=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds := by rfl
theorem a_profile115_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a115=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a115.bounds := by rfl
theorem r_fixed115_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 7 := by decide +kernel
theorem a_fixed115_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a115.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.a115.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 9 := by decide +kernel
theorem ranks115_linked : ReferenceRankData.CoarseLowerShape.Batch0014.targetR115=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0014.targetA115=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 1 := by decide +kernel
theorem r_input115_linked : ReferenceRankData.CoarseLowerShape.Batch0014.r115.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds.gauge] := by decide +kernel
theorem a_input115_linked : ReferenceRankData.CoarseLowerShape.Batch0014.a115.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.a115.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.a115.bounds.gauge] := by decide +kernel
theorem geometry115_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.a := by decide +kernel
theorem weights230_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0028.cert230.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights231_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0028.cert231.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time115_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 10)=true := by decide +kernel
theorem r_reference115_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 0)=true := by decide +kernel
theorem a_reference115_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 1)=true := by decide +kernel
theorem rank_r_link115_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r115 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link115_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0014.a115.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a115 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints115 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell true ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r115 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile115_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link115_checked
    geometry115_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell false ReferenceProfileData.CoarseLowerShape.Batch0014.a115.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a115 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile115_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link115_checked
    geometry115_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks115_linked.1,←ranks115_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0014.r115.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a115.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0014.ordered115_checked hr ha ho
theorem frozen_frame115 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115 ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds ReferenceProfileData.CoarseLowerShape.Batch0014.a115.bounds
  · rw [←r_profile115_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile115_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry115_linked.2.2.2.2.1
  · exact geometry115_linked.2.2.2.2.2
  · exact r_reference115_checked
  · exact a_reference115_checked
  · exact r_fixed115_linked
  · exact a_fixed115_linked
  · exact time115_checked
  · exact ht
  · exact hw
theorem child_geometry115_checked : ReferenceWeightData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights115 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0028.cert230∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch28_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0028.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0028.cert231∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch28_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0028.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0028.cert230.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry115_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights230_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0028.cert231.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry115_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry115_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights231_linked j (List.mem_finRange j))
theorem actual_frozen_frame115 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame115 (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.flow.timeParameter_mem child_geometry115_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights115 hz)
theorem r_profile116_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r116=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds := by rfl
theorem a_profile116_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a116=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a116.bounds := by rfl
theorem r_fixed116_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 7 := by decide +kernel
theorem a_fixed116_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a116.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.a116.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 9 := by decide +kernel
theorem ranks116_linked : ReferenceRankData.CoarseLowerShape.Batch0014.targetR116=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0014.targetA116=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 1 := by decide +kernel
theorem r_input116_linked : ReferenceRankData.CoarseLowerShape.Batch0014.r116.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds.gauge] := by decide +kernel
theorem a_input116_linked : ReferenceRankData.CoarseLowerShape.Batch0014.a116.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.a116.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.a116.bounds.gauge] := by decide +kernel
theorem geometry116_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.a := by decide +kernel
theorem weights232_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0029.cert232.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights233_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0029.cert233.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time116_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 10)=true := by decide +kernel
theorem r_reference116_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 0)=true := by decide +kernel
theorem a_reference116_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 1)=true := by decide +kernel
theorem rank_r_link116_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r116 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link116_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0014.a116.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a116 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints116 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell true ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r116 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile116_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link116_checked
    geometry116_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell false ReferenceProfileData.CoarseLowerShape.Batch0014.a116.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a116 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile116_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link116_checked
    geometry116_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks116_linked.1,←ranks116_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0014.r116.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a116.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0014.ordered116_checked hr ha ho
theorem frozen_frame116 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116 ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds ReferenceProfileData.CoarseLowerShape.Batch0014.a116.bounds
  · rw [←r_profile116_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile116_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry116_linked.2.2.2.2.1
  · exact geometry116_linked.2.2.2.2.2
  · exact r_reference116_checked
  · exact a_reference116_checked
  · exact r_fixed116_linked
  · exact a_fixed116_linked
  · exact time116_checked
  · exact ht
  · exact hw
theorem child_geometry116_checked : ReferenceWeightData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights116 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0029.cert232∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch29_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0029.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0029.cert233∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch29_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0029.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0029.cert232.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry116_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights232_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0029.cert233.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry116_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry116_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights233_linked j (List.mem_finRange j))
theorem actual_frozen_frame116 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame116 (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.flow.timeParameter_mem child_geometry116_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights116 hz)
theorem r_profile117_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r117=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds := by rfl
theorem a_profile117_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a117=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a117.bounds := by rfl
theorem r_fixed117_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 7 := by decide +kernel
theorem a_fixed117_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a117.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.a117.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 9 := by decide +kernel
theorem ranks117_linked : ReferenceRankData.CoarseLowerShape.Batch0014.targetR117=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0014.targetA117=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 1 := by decide +kernel
theorem r_input117_linked : ReferenceRankData.CoarseLowerShape.Batch0014.r117.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds.gauge] := by decide +kernel
theorem a_input117_linked : ReferenceRankData.CoarseLowerShape.Batch0014.a117.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.a117.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.a117.bounds.gauge] := by decide +kernel
theorem geometry117_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.a := by decide +kernel
theorem weights234_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0029.cert234.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights235_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0029.cert235.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time117_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 10)=true := by decide +kernel
theorem r_reference117_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 0)=true := by decide +kernel
theorem a_reference117_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 1)=true := by decide +kernel
theorem rank_r_link117_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r117 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link117_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0014.a117.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a117 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints117 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell true ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r117 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile117_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link117_checked
    geometry117_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell false ReferenceProfileData.CoarseLowerShape.Batch0014.a117.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a117 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile117_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link117_checked
    geometry117_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks117_linked.1,←ranks117_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0014.r117.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a117.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0014.ordered117_checked hr ha ho
theorem frozen_frame117 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117 ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds ReferenceProfileData.CoarseLowerShape.Batch0014.a117.bounds
  · rw [←r_profile117_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile117_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry117_linked.2.2.2.2.1
  · exact geometry117_linked.2.2.2.2.2
  · exact r_reference117_checked
  · exact a_reference117_checked
  · exact r_fixed117_linked
  · exact a_fixed117_linked
  · exact time117_checked
  · exact ht
  · exact hw
theorem child_geometry117_checked : ReferenceWeightData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights117 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0029.cert234∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch29_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0029.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0029.cert235∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch29_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0029.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0029.cert234.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry117_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights234_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0029.cert235.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry117_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry117_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights235_linked j (List.mem_finRange j))
theorem actual_frozen_frame117 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame117 (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.flow.timeParameter_mem child_geometry117_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights117 hz)
theorem r_profile118_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r118=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds := by rfl
theorem a_profile118_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a118=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a118.bounds := by rfl
theorem r_fixed118_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 7 := by decide +kernel
theorem a_fixed118_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a118.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.a118.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 9 := by decide +kernel
theorem ranks118_linked : ReferenceRankData.CoarseLowerShape.Batch0014.targetR118=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0014.targetA118=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 1 := by decide +kernel
theorem r_input118_linked : ReferenceRankData.CoarseLowerShape.Batch0014.r118.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds.gauge] := by decide +kernel
theorem a_input118_linked : ReferenceRankData.CoarseLowerShape.Batch0014.a118.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.a118.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.a118.bounds.gauge] := by decide +kernel
theorem geometry118_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.a := by decide +kernel
theorem weights236_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0029.cert236.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights237_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0029.cert237.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time118_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 10)=true := by decide +kernel
theorem r_reference118_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 0)=true := by decide +kernel
theorem a_reference118_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 1)=true := by decide +kernel
theorem rank_r_link118_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r118 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link118_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0014.a118.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a118 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints118 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell true ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r118 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile118_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link118_checked
    geometry118_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell false ReferenceProfileData.CoarseLowerShape.Batch0014.a118.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a118 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile118_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link118_checked
    geometry118_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks118_linked.1,←ranks118_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0014.r118.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a118.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0014.ordered118_checked hr ha ho
theorem frozen_frame118 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118 ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds ReferenceProfileData.CoarseLowerShape.Batch0014.a118.bounds
  · rw [←r_profile118_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile118_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry118_linked.2.2.2.2.1
  · exact geometry118_linked.2.2.2.2.2
  · exact r_reference118_checked
  · exact a_reference118_checked
  · exact r_fixed118_linked
  · exact a_fixed118_linked
  · exact time118_checked
  · exact ht
  · exact hw
theorem child_geometry118_checked : ReferenceWeightData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights118 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0029.cert236∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch29_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0029.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0029.cert237∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch29_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0029.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0029.cert236.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry118_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights236_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0029.cert237.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry118_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry118_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights237_linked j (List.mem_finRange j))
theorem actual_frozen_frame118 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame118 (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.flow.timeParameter_mem child_geometry118_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights118 hz)
theorem r_profile119_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r119=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds := by rfl
theorem a_profile119_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a119=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a119.bounds := by rfl
theorem r_fixed119_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 7 := by decide +kernel
theorem a_fixed119_linked : ReferenceProfileData.CoarseLowerShape.Batch0014.a119.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0014.a119.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 9 := by decide +kernel
theorem ranks119_linked : ReferenceRankData.CoarseLowerShape.Batch0014.targetR119=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0014.targetA119=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 1 := by decide +kernel
theorem r_input119_linked : ReferenceRankData.CoarseLowerShape.Batch0014.r119.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds.gauge] := by decide +kernel
theorem a_input119_linked : ReferenceRankData.CoarseLowerShape.Batch0014.a119.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0014.a119.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0014.a119.bounds.gauge] := by decide +kernel
theorem geometry119_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.a := by decide +kernel
theorem weights238_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0029.cert238.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights239_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0029.cert239.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time119_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 10)=true := by decide +kernel
theorem r_reference119_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 0)=true := by decide +kernel
theorem a_reference119_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 1)=true := by decide +kernel
theorem rank_r_link119_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r119 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link119_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0014.a119.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a119 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints119 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell true ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds ReferenceRankData.CoarseLowerShape.Batch0014.r119 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile119_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link119_checked
    geometry119_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell false ReferenceProfileData.CoarseLowerShape.Batch0014.a119.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a119 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile119_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0014.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0014.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link119_checked
    geometry119_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks119_linked.1,←ranks119_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0014.r119.bounds ReferenceRankData.CoarseLowerShape.Batch0014.a119.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0014.ordered119_checked hr ha ho
theorem frozen_frame119 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119 ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds ReferenceProfileData.CoarseLowerShape.Batch0014.a119.bounds
  · rw [←r_profile119_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile119_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry119_linked.2.2.2.2.1
  · exact geometry119_linked.2.2.2.2.2
  · exact r_reference119_checked
  · exact a_reference119_checked
  · exact r_fixed119_linked
  · exact a_fixed119_linked
  · exact time119_checked
  · exact ht
  · exact hw
theorem child_geometry119_checked : ReferenceWeightData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights119 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0029.cert238∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch29_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0029.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0029.cert239∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch29_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0029.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0029.cert238.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry119_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights238_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0029.cert239.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry119_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry119_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights239_linked j (List.mem_finRange j))
theorem actual_frozen_frame119 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame119 (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.flow.timeParameter_mem child_geometry119_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights119 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell112),(ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell113),(ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell114),(ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell115),(ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell116),(ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell117),(ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell118),(ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0014.cell119)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0014.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0014.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame112 hz
  · exact fun z hz=>actual_frozen_frame113 hz
  · exact fun z hz=>actual_frozen_frame114 hz
  · exact fun z hz=>actual_frozen_frame115 hz
  · exact fun z hz=>actual_frozen_frame116 hz
  · exact fun z hz=>actual_frozen_frame117 hz
  · exact fun z hz=>actual_frozen_frame118 hz
  · exact fun z hz=>actual_frozen_frame119 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints112 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints113 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints114 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints115 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints116 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints117 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints118 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints119 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry112_linked.1,geometry112_linked.2.1,geometry112_linked.2.2.1,geometry112_linked.2.2.2.1⟩
  · exact ⟨geometry113_linked.1,geometry113_linked.2.1,geometry113_linked.2.2.1,geometry113_linked.2.2.2.1⟩
  · exact ⟨geometry114_linked.1,geometry114_linked.2.1,geometry114_linked.2.2.1,geometry114_linked.2.2.2.1⟩
  · exact ⟨geometry115_linked.1,geometry115_linked.2.1,geometry115_linked.2.2.1,geometry115_linked.2.2.2.1⟩
  · exact ⟨geometry116_linked.1,geometry116_linked.2.1,geometry116_linked.2.2.1,geometry116_linked.2.2.2.1⟩
  · exact ⟨geometry117_linked.1,geometry117_linked.2.1,geometry117_linked.2.2.1,geometry117_linked.2.2.2.1⟩
  · exact ⟨geometry118_linked.1,geometry118_linked.2.1,geometry118_linked.2.2.1,geometry118_linked.2.2.2.1⟩
  · exact ⟨geometry119_linked.1,geometry119_linked.2.1,geometry119_linked.2.2.1,geometry119_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.a112.bounds,?_,geometry112_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a112.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile112_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds,?_,geometry112_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert112.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r112.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile112_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.a113.bounds,?_,geometry113_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a113.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile113_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds,?_,geometry113_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert113.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r113.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile113_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.a114.bounds,?_,geometry114_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a114.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile114_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds,?_,geometry114_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert114.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r114.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile114_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.a115.bounds,?_,geometry115_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a115.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile115_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds,?_,geometry115_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert115.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r115.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile115_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.a116.bounds,?_,geometry116_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a116.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile116_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds,?_,geometry116_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert116.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r116.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile116_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.a117.bounds,?_,geometry117_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a117.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile117_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds,?_,geometry117_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert117.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r117.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile117_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.a118.bounds,?_,geometry118_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a118.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile118_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds,?_,geometry118_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert118.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r118.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile118_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.a119.bounds,?_,geometry119_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0014.a119.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile119_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds,?_,geometry119_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0014.cert119.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0014.r119.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile119_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0014.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0014.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0014

namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0015
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem weight_batch30_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0030.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0030.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem weight_batch31_mem {w : Transport.ReferenceWeightCertificate} (hw : w∈ReferenceWeightData.CoarseLowerShape.Batch0031.certificates) : w∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := by
  unfold ReferenceWeightData.CoarseLowerShape.Assembly.certificates
  apply List.mem_flatten.mpr
  refine ⟨ReferenceWeightData.CoarseLowerShape.Batch0031.certificates,?_,hw⟩
  simp only [List.mem_cons,List.mem_singleton]; tauto
theorem r_profile120_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r120=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds := by rfl
theorem a_profile120_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a120=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a120.bounds := by rfl
theorem r_fixed120_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 7 := by decide +kernel
theorem a_fixed120_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a120.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.a120.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 9 := by decide +kernel
theorem ranks120_linked : ReferenceRankData.CoarseLowerShape.Batch0015.targetR120=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0015.targetA120=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 1 := by decide +kernel
theorem r_input120_linked : ReferenceRankData.CoarseLowerShape.Batch0015.r120.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds.gauge] := by decide +kernel
theorem a_input120_linked : ReferenceRankData.CoarseLowerShape.Batch0015.a120.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.a120.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.a120.bounds.gauge] := by decide +kernel
theorem geometry120_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.a := by decide +kernel
theorem weights240_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0030.cert240.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights241_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0030.cert241.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time120_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 10)=true := by decide +kernel
theorem r_reference120_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 0)=true := by decide +kernel
theorem a_reference120_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 1)=true := by decide +kernel
theorem rank_r_link120_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r120 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link120_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0015.a120.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a120 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints120 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell true ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r120 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile120_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link120_checked
    geometry120_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell false ReferenceProfileData.CoarseLowerShape.Batch0015.a120.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a120 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile120_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link120_checked
    geometry120_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks120_linked.1,←ranks120_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0015.r120.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a120.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0015.ordered120_checked hr ha ho
theorem frozen_frame120 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120 ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds ReferenceProfileData.CoarseLowerShape.Batch0015.a120.bounds
  · rw [←r_profile120_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile120_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry120_linked.2.2.2.2.1
  · exact geometry120_linked.2.2.2.2.2
  · exact r_reference120_checked
  · exact a_reference120_checked
  · exact r_fixed120_linked
  · exact a_fixed120_linked
  · exact time120_checked
  · exact ht
  · exact hw
theorem child_geometry120_checked : ReferenceWeightData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights120 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0030.cert240∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch30_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0030.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0030.cert241∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch30_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0030.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0030.cert240.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry120_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights240_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0030.cert241.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry120_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry120_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights241_linked j (List.mem_finRange j))
theorem actual_frozen_frame120 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame120 (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.flow.timeParameter_mem child_geometry120_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights120 hz)
theorem r_profile121_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r121=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds := by rfl
theorem a_profile121_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a121=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a121.bounds := by rfl
theorem r_fixed121_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 7 := by decide +kernel
theorem a_fixed121_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a121.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.a121.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 9 := by decide +kernel
theorem ranks121_linked : ReferenceRankData.CoarseLowerShape.Batch0015.targetR121=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0015.targetA121=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 1 := by decide +kernel
theorem r_input121_linked : ReferenceRankData.CoarseLowerShape.Batch0015.r121.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds.gauge] := by decide +kernel
theorem a_input121_linked : ReferenceRankData.CoarseLowerShape.Batch0015.a121.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.a121.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.a121.bounds.gauge] := by decide +kernel
theorem geometry121_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.a := by decide +kernel
theorem weights242_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0030.cert242.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights243_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0030.cert243.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time121_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 10)=true := by decide +kernel
theorem r_reference121_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 0)=true := by decide +kernel
theorem a_reference121_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 1)=true := by decide +kernel
theorem rank_r_link121_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r121 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link121_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0015.a121.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a121 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints121 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell true ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r121 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile121_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link121_checked
    geometry121_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell false ReferenceProfileData.CoarseLowerShape.Batch0015.a121.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a121 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile121_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link121_checked
    geometry121_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks121_linked.1,←ranks121_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0015.r121.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a121.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0015.ordered121_checked hr ha ho
theorem frozen_frame121 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121 ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds ReferenceProfileData.CoarseLowerShape.Batch0015.a121.bounds
  · rw [←r_profile121_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile121_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry121_linked.2.2.2.2.1
  · exact geometry121_linked.2.2.2.2.2
  · exact r_reference121_checked
  · exact a_reference121_checked
  · exact r_fixed121_linked
  · exact a_fixed121_linked
  · exact time121_checked
  · exact ht
  · exact hw
theorem child_geometry121_checked : ReferenceWeightData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights121 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0030.cert242∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch30_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0030.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0030.cert243∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch30_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0030.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0030.cert242.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry121_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights242_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0030.cert243.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry121_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry121_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights243_linked j (List.mem_finRange j))
theorem actual_frozen_frame121 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame121 (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.flow.timeParameter_mem child_geometry121_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights121 hz)
theorem r_profile122_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r122=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds := by rfl
theorem a_profile122_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a122=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a122.bounds := by rfl
theorem r_fixed122_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 7 := by decide +kernel
theorem a_fixed122_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a122.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.a122.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 9 := by decide +kernel
theorem ranks122_linked : ReferenceRankData.CoarseLowerShape.Batch0015.targetR122=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0015.targetA122=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 1 := by decide +kernel
theorem r_input122_linked : ReferenceRankData.CoarseLowerShape.Batch0015.r122.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds.gauge] := by decide +kernel
theorem a_input122_linked : ReferenceRankData.CoarseLowerShape.Batch0015.a122.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.a122.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.a122.bounds.gauge] := by decide +kernel
theorem geometry122_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.a := by decide +kernel
theorem weights244_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0030.cert244.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights245_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0030.cert245.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time122_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 10)=true := by decide +kernel
theorem r_reference122_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 0)=true := by decide +kernel
theorem a_reference122_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 1)=true := by decide +kernel
theorem rank_r_link122_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r122 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link122_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0015.a122.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a122 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints122 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell true ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r122 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile122_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link122_checked
    geometry122_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell false ReferenceProfileData.CoarseLowerShape.Batch0015.a122.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a122 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile122_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link122_checked
    geometry122_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks122_linked.1,←ranks122_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0015.r122.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a122.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0015.ordered122_checked hr ha ho
theorem frozen_frame122 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122 ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds ReferenceProfileData.CoarseLowerShape.Batch0015.a122.bounds
  · rw [←r_profile122_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile122_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry122_linked.2.2.2.2.1
  · exact geometry122_linked.2.2.2.2.2
  · exact r_reference122_checked
  · exact a_reference122_checked
  · exact r_fixed122_linked
  · exact a_fixed122_linked
  · exact time122_checked
  · exact ht
  · exact hw
theorem child_geometry122_checked : ReferenceWeightData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights122 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0030.cert244∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch30_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0030.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0030.cert245∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch30_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0030.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0030.cert244.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry122_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights244_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0030.cert245.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry122_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry122_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights245_linked j (List.mem_finRange j))
theorem actual_frozen_frame122 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame122 (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.flow.timeParameter_mem child_geometry122_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights122 hz)
theorem r_profile123_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r123=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds := by rfl
theorem a_profile123_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a123=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a123.bounds := by rfl
theorem r_fixed123_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 7 := by decide +kernel
theorem a_fixed123_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a123.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.a123.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 9 := by decide +kernel
theorem ranks123_linked : ReferenceRankData.CoarseLowerShape.Batch0015.targetR123=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0015.targetA123=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 1 := by decide +kernel
theorem r_input123_linked : ReferenceRankData.CoarseLowerShape.Batch0015.r123.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds.gauge] := by decide +kernel
theorem a_input123_linked : ReferenceRankData.CoarseLowerShape.Batch0015.a123.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.a123.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.a123.bounds.gauge] := by decide +kernel
theorem geometry123_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.a := by decide +kernel
theorem weights246_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0030.cert246.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights247_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0030.cert247.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time123_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 10)=true := by decide +kernel
theorem r_reference123_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 0)=true := by decide +kernel
theorem a_reference123_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 1)=true := by decide +kernel
theorem rank_r_link123_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r123 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link123_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0015.a123.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a123 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints123 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell true ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r123 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile123_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link123_checked
    geometry123_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell false ReferenceProfileData.CoarseLowerShape.Batch0015.a123.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a123 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile123_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link123_checked
    geometry123_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks123_linked.1,←ranks123_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0015.r123.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a123.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0015.ordered123_checked hr ha ho
theorem frozen_frame123 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123 ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds ReferenceProfileData.CoarseLowerShape.Batch0015.a123.bounds
  · rw [←r_profile123_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile123_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry123_linked.2.2.2.2.1
  · exact geometry123_linked.2.2.2.2.2
  · exact r_reference123_checked
  · exact a_reference123_checked
  · exact r_fixed123_linked
  · exact a_fixed123_linked
  · exact time123_checked
  · exact ht
  · exact hw
theorem child_geometry123_checked : ReferenceWeightData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights123 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0030.cert246∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch30_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0030.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0030.cert247∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch30_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0030.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0030.cert246.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry123_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights246_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0030.cert247.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry123_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry123_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights247_linked j (List.mem_finRange j))
theorem actual_frozen_frame123 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame123 (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.flow.timeParameter_mem child_geometry123_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights123 hz)
theorem r_profile124_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r124=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds := by rfl
theorem a_profile124_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a124=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a124.bounds := by rfl
theorem r_fixed124_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 7 := by decide +kernel
theorem a_fixed124_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a124.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.a124.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 9 := by decide +kernel
theorem ranks124_linked : ReferenceRankData.CoarseLowerShape.Batch0015.targetR124=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0015.targetA124=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 1 := by decide +kernel
theorem r_input124_linked : ReferenceRankData.CoarseLowerShape.Batch0015.r124.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds.gauge] := by decide +kernel
theorem a_input124_linked : ReferenceRankData.CoarseLowerShape.Batch0015.a124.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.a124.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.a124.bounds.gauge] := by decide +kernel
theorem geometry124_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.a := by decide +kernel
theorem weights248_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0031.cert248.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights249_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0031.cert249.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time124_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 10)=true := by decide +kernel
theorem r_reference124_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 0)=true := by decide +kernel
theorem a_reference124_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 1)=true := by decide +kernel
theorem rank_r_link124_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r124 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link124_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0015.a124.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a124 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints124 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell true ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r124 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile124_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link124_checked
    geometry124_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell false ReferenceProfileData.CoarseLowerShape.Batch0015.a124.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a124 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile124_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link124_checked
    geometry124_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks124_linked.1,←ranks124_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0015.r124.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a124.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0015.ordered124_checked hr ha ho
theorem frozen_frame124 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124 ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds ReferenceProfileData.CoarseLowerShape.Batch0015.a124.bounds
  · rw [←r_profile124_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile124_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry124_linked.2.2.2.2.1
  · exact geometry124_linked.2.2.2.2.2
  · exact r_reference124_checked
  · exact a_reference124_checked
  · exact r_fixed124_linked
  · exact a_fixed124_linked
  · exact time124_checked
  · exact ht
  · exact hw
theorem child_geometry124_checked : ReferenceWeightData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights124 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0031.cert248∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch31_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0031.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0031.cert249∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch31_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0031.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0031.cert248.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry124_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights248_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0031.cert249.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry124_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry124_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights249_linked j (List.mem_finRange j))
theorem actual_frozen_frame124 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame124 (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.flow.timeParameter_mem child_geometry124_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights124 hz)
theorem r_profile125_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r125=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds := by rfl
theorem a_profile125_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a125=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a125.bounds := by rfl
theorem r_fixed125_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 7 := by decide +kernel
theorem a_fixed125_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a125.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.a125.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 9 := by decide +kernel
theorem ranks125_linked : ReferenceRankData.CoarseLowerShape.Batch0015.targetR125=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0015.targetA125=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 1 := by decide +kernel
theorem r_input125_linked : ReferenceRankData.CoarseLowerShape.Batch0015.r125.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds.gauge] := by decide +kernel
theorem a_input125_linked : ReferenceRankData.CoarseLowerShape.Batch0015.a125.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.a125.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.a125.bounds.gauge] := by decide +kernel
theorem geometry125_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.a := by decide +kernel
theorem weights250_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0031.cert250.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights251_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0031.cert251.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time125_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 10)=true := by decide +kernel
theorem r_reference125_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 0)=true := by decide +kernel
theorem a_reference125_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 1)=true := by decide +kernel
theorem rank_r_link125_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r125 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link125_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0015.a125.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a125 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints125 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell true ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r125 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile125_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link125_checked
    geometry125_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell false ReferenceProfileData.CoarseLowerShape.Batch0015.a125.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a125 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile125_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link125_checked
    geometry125_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks125_linked.1,←ranks125_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0015.r125.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a125.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0015.ordered125_checked hr ha ho
theorem frozen_frame125 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125 ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds ReferenceProfileData.CoarseLowerShape.Batch0015.a125.bounds
  · rw [←r_profile125_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile125_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry125_linked.2.2.2.2.1
  · exact geometry125_linked.2.2.2.2.2
  · exact r_reference125_checked
  · exact a_reference125_checked
  · exact r_fixed125_linked
  · exact a_fixed125_linked
  · exact time125_checked
  · exact ht
  · exact hw
theorem child_geometry125_checked : ReferenceWeightData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights125 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0031.cert250∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch31_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0031.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0031.cert251∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch31_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0031.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0031.cert250.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry125_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights250_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0031.cert251.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry125_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry125_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights251_linked j (List.mem_finRange j))
theorem actual_frozen_frame125 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame125 (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.flow.timeParameter_mem child_geometry125_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights125 hz)
theorem r_profile126_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r126=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds := by rfl
theorem a_profile126_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a126=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a126.bounds := by rfl
theorem r_fixed126_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 7 := by decide +kernel
theorem a_fixed126_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a126.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.a126.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 9 := by decide +kernel
theorem ranks126_linked : ReferenceRankData.CoarseLowerShape.Batch0015.targetR126=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0015.targetA126=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 1 := by decide +kernel
theorem r_input126_linked : ReferenceRankData.CoarseLowerShape.Batch0015.r126.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds.gauge] := by decide +kernel
theorem a_input126_linked : ReferenceRankData.CoarseLowerShape.Batch0015.a126.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.a126.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.a126.bounds.gauge] := by decide +kernel
theorem geometry126_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.a := by decide +kernel
theorem weights252_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0031.cert252.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights253_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0031.cert253.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time126_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 10)=true := by decide +kernel
theorem r_reference126_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 0)=true := by decide +kernel
theorem a_reference126_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 1)=true := by decide +kernel
theorem rank_r_link126_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r126 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link126_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0015.a126.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a126 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints126 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell true ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r126 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile126_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link126_checked
    geometry126_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell false ReferenceProfileData.CoarseLowerShape.Batch0015.a126.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a126 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile126_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link126_checked
    geometry126_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks126_linked.1,←ranks126_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0015.r126.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a126.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0015.ordered126_checked hr ha ho
theorem frozen_frame126 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126 ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds ReferenceProfileData.CoarseLowerShape.Batch0015.a126.bounds
  · rw [←r_profile126_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile126_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry126_linked.2.2.2.2.1
  · exact geometry126_linked.2.2.2.2.2
  · exact r_reference126_checked
  · exact a_reference126_checked
  · exact r_fixed126_linked
  · exact a_fixed126_linked
  · exact time126_checked
  · exact ht
  · exact hw
theorem child_geometry126_checked : ReferenceWeightData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights126 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0031.cert252∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch31_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0031.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0031.cert253∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch31_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0031.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0031.cert252.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry126_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights252_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0031.cert253.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry126_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry126_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights253_linked j (List.mem_finRange j))
theorem actual_frozen_frame126 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame126 (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.flow.timeParameter_mem child_geometry126_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights126 hz)
theorem r_profile127_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r127=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds := by rfl
theorem a_profile127_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a127=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a127.bounds := by rfl
theorem r_fixed127_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds.primitive=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 2 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 6 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds.gauge=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 3 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 7 := by decide +kernel
theorem a_fixed127_linked : ReferenceProfileData.CoarseLowerShape.Batch0015.a127.bounds.score=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 8 ∧ ReferenceProfileData.CoarseLowerShape.Batch0015.a127.bounds.gaugeDerivative=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 9 := by decide +kernel
theorem ranks127_linked : ReferenceRankData.CoarseLowerShape.Batch0015.targetR127=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 0 ∧ ReferenceRankData.CoarseLowerShape.Batch0015.targetA127=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 1 := by decide +kernel
theorem r_input127_linked : ReferenceRankData.CoarseLowerShape.Batch0015.r127.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds.gauge] := by decide +kernel
theorem a_input127_linked : ReferenceRankData.CoarseLowerShape.Batch0015.a127.tube.input=![ReferenceProfileData.CoarseLowerShape.scalarBox,ReferenceProfileData.CoarseLowerShape.Batch0015.a127.bounds.primitive,ReferenceProfileData.CoarseLowerShape.Batch0015.a127.bounds.gauge] := by decide +kernel
theorem geometry127_linked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.late=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.late ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.zLo ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.z=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.zHi ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.r≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.r ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.a≤ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.a := by decide +kernel
theorem weights254_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0031.cert254.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem weights255_linked : (List.finRange 4).all (fun j=>(ReferenceWeightData.CoarseLowerShape.Batch0031.cert255.cell.weights j).subsetCheck (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed ⟨11+j.val,by omega⟩))=true := by decide +kernel
theorem time127_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.timeBoundsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.scale (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 4) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 5) (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 10)=true := by decide +kernel
theorem r_reference127_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.r ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.r (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 0)=true := by decide +kernel
theorem a_reference127_checked : IntegerInterval.rationalEndpointsCheck ReferenceSensitivityData.CoarseLowerShape.scale ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.a ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.a (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 1)=true := by decide +kernel
theorem rank_r_link127_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.rankLinkCheck true ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r127 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem rank_a_link127_checked : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.rankLinkCheck false ReferenceProfileData.CoarseLowerShape.Batch0015.a127.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a127 ReferenceProfileData.CoarseLowerShape.scalarBox=true := by decide +kernel
theorem matched_endpoints127 {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hobstacle : ∀ r∈Set.Icc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.leftContact:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.rightContact,quadratic ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.lam r-S≤J r ∧ J r≤cap ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.lam S r)
    (hS : ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S)
    {t r a : ℝ} (ht : t∈Set.Icc (0:ℝ) 1)
    (hR : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.primitiveMatch true S J t r) (hA : ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.primitiveMatch false S J t a)
    (ho : if ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.late then a≤r else r≤a) :
    (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  have hr := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell true ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds ReferenceRankData.CoarseLowerShape.Batch0015.r127 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_pos rfl,←r_profile127_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_r_link127_checked
    geometry127_linked.2.2.2.2.1 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hR
  have ha := Transport.ReferenceScalarCell.checked_primitive_matched_rank
    (s:=ReferenceSensitivityData.CoarseLowerShape.scale) (k:=ReferenceRankData.CoarseLowerShape.multiplier)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceRankData.CoarseLowerShape.multiplier])
    ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell false ReferenceProfileData.CoarseLowerShape.Batch0015.a127.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a127 ReferenceProfileData.CoarseLowerShape.scalarBox
    (by rw [Transport.ReferenceScalarCell.rankProfile,if_neg Bool.false_ne_true,←a_profile127_linked]; exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto))
    (List.all_eq_true.mp ReferenceRankData.CoarseLowerShape.Batch0015.checked _ (by simp only [ReferenceRankData.CoarseLowerShape.Batch0015.ranks,List.mem_cons,List.mem_singleton]; tauto)) rank_a_link127_checked
    geometry127_linked.2.2.2.2.2 hL hSl
    (by change Variational.ell≤(TransportReferenceData.CoarseLowerShape.leftContact:ℝ); norm_num [Variational.ell,TransportReferenceData.CoarseLowerShape.leftContact])
    (by change (TransportReferenceData.CoarseLowerShape.rightContact:ℝ)≤Variational.tEnd; norm_num [Variational.tEnd,TransportReferenceData.CoarseLowerShape.rightContact]) hobstacle hS ht hA
  rw [←ranks127_linked.1,←ranks127_linked.2]
  exact IntegerInterval.orderedRanksCheck_sound ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.late ReferenceRankData.CoarseLowerShape.Batch0015.r127.bounds ReferenceRankData.CoarseLowerShape.Batch0015.a127.bounds _ _ ReferenceRankData.CoarseLowerShape.Batch0015.ordered127_checked hr ha ho
theorem frozen_frame127 {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) (w : Fin 4→ℝ)
    (hw : ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (w j)) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.weightedInput t w j.succ) := by
  apply Transport.ReferenceScalarCell.checked_frozen_frame (k:=ReferenceSensitivityData.CoarseLowerShape.scale)
    (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) (by norm_num [ReferenceSensitivityData.CoarseLowerShape.scale]) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127 ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds ReferenceProfileData.CoarseLowerShape.Batch0015.a127.bounds
  · rw [←r_profile127_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · rw [←a_profile127_linked]
    exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.profiles_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · exact geometry127_linked.2.2.2.2.1
  · exact geometry127_linked.2.2.2.2.2
  · exact r_reference127_checked
  · exact a_reference127_checked
  · exact r_fixed127_linked
  · exact a_fixed127_linked
  · exact time127_checked
  · exact ht
  · exact hw
theorem child_geometry127_checked : ReferenceWeightData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.z=ReferenceWeightData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.z ∧ ReferenceWeightData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.z=ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.z ∧ ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.z<ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.z := by decide +kernel
theorem actual_weights127 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed ⟨11+j.val,by omega⟩).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceAdjointData.CoarseLowerShape.weight j z) := by
  have hmem0 : ReferenceWeightData.CoarseLowerShape.Batch0031.cert254∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch31_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0031.certificates,List.mem_cons,List.mem_singleton]; tauto)
  have hmem1 : ReferenceWeightData.CoarseLowerShape.Batch0031.cert255∈ReferenceWeightData.CoarseLowerShape.Assembly.certificates := weight_batch31_mem (by simp only [ReferenceWeightData.CoarseLowerShape.Batch0031.certificates,List.mem_cons,List.mem_singleton]; tauto)
  by_cases he : z≤(ReferenceWeightData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.z:ℝ)
  · have hz0 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0031.cert254.cell.flow.segment.right.z := by
      exact ⟨by simpa only [child_geometry127_checked.1] using hz.1,he⟩
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem0 hz0 j)
      (List.all_eq_true.mp weights254_linked j (List.mem_finRange j))
  · have hz1 : z∈Set.Ioc (ReferenceWeightData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.left.z:ℝ) ReferenceWeightData.CoarseLowerShape.Batch0031.cert255.cell.flow.segment.right.z := by
      constructor
      · rw [←child_geometry127_checked.2.1]; exact lt_of_not_ge he
      · simpa only [child_geometry127_checked.2.2.1] using hz.2
    intro j
    exact IntegerInterval.subsetCheck_sound (ReferenceAdjointData.CoarseLowerShape.weights_contain hmem1 hz1 j)
      (List.all_eq_true.mp weights255_linked j (List.mem_finRange j))
theorem actual_frozen_frame127 {z : ℝ} (hz : z∈Set.Ioc (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.left.z:ℝ) ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.segment.right.z) :
    ∀ j,(TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.weightedInput (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  exact frozen_frame127 (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.flow.timeParameter_mem child_geometry127_checked.2.2.2 ⟨hz.1.le,hz.2⟩) _ (actual_weights127 hz)
def sources : List (Transport.ReferenceScalarCell×Transport.HessianCell) := [(ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell120),(ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell121),(ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell122),(ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell123),(ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell124),(ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell125),(ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell126),(ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell,TransportHessianData.CoarseLowerShapeFlow.Batch0015.cell127)]
theorem sources_cells : sources.map (fun p=>p.1.flow)=ReferenceSensitivityData.CoarseLowerShape.Batch0015.certificates.map (fun c=>c.cell.flow) := by rfl
theorem sources_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.Batch0015.cells := by rfl
theorem actual_frames : ∀ p∈sources,∀ z∈Set.Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun z hz=>actual_frozen_frame120 hz
  · exact fun z hz=>actual_frozen_frame121 hz
  · exact fun z hz=>actual_frozen_frame122 hz
  · exact fun z hz=>actual_frozen_frame123 hz
  · exact fun z hz=>actual_frozen_frame124 hz
  · exact fun z hz=>actual_frozen_frame125 hz
  · exact fun z hz=>actual_frozen_frame126 hz
  · exact fun z hz=>actual_frozen_frame127 hz
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Set.Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints120 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints121 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints122 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints123 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints124 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints125 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints126 hL hSl hobstacle hS ht hR hA ho
  · exact fun S J hL hSl hobstacle hS t ht r a hR hA ho=>matched_endpoints127 hL hSl hobstacle hS ht hR hA ho
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨geometry120_linked.1,geometry120_linked.2.1,geometry120_linked.2.2.1,geometry120_linked.2.2.2.1⟩
  · exact ⟨geometry121_linked.1,geometry121_linked.2.1,geometry121_linked.2.2.1,geometry121_linked.2.2.2.1⟩
  · exact ⟨geometry122_linked.1,geometry122_linked.2.1,geometry122_linked.2.2.1,geometry122_linked.2.2.2.1⟩
  · exact ⟨geometry123_linked.1,geometry123_linked.2.1,geometry123_linked.2.2.1,geometry123_linked.2.2.2.1⟩
  · exact ⟨geometry124_linked.1,geometry124_linked.2.1,geometry124_linked.2.2.1,geometry124_linked.2.2.2.1⟩
  · exact ⟨geometry125_linked.1,geometry125_linked.2.1,geometry125_linked.2.2.1,geometry125_linked.2.2.2.1⟩
  · exact ⟨geometry126_linked.1,geometry126_linked.2.1,geometry126_linked.2.2.1,geometry126_linked.2.2.2.1⟩
  · exact ⟨geometry127_linked.1,geometry127_linked.2.1,geometry127_linked.2.2.1,geometry127_linked.2.2.2.1⟩
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
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.a120.bounds,?_,geometry120_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a120.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile120_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds,?_,geometry120_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert120.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r120.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile120_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.a121.bounds,?_,geometry121_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a121.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile121_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds,?_,geometry121_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert121.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r121.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile121_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.a122.bounds,?_,geometry122_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a122.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile122_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds,?_,geometry122_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert122.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r122.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile122_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.a123.bounds,?_,geometry123_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a123.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile123_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds,?_,geometry123_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert123.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r123.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile123_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.a124.bounds,?_,geometry124_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a124.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile124_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds,?_,geometry124_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert124.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r124.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile124_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.a125.bounds,?_,geometry125_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a125.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile125_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds,?_,geometry125_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert125.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r125.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile125_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.a126.bounds,?_,geometry126_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a126.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile126_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds,?_,geometry126_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert126.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r126.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile126_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
  · intro useR
    cases useR
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.a127.bounds,?_,geometry127_linked.2.2.2.2.2⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.aProfile ReferenceProfileData.CoarseLowerShape.Batch0015.a127.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←a_profile127_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
    · refine ⟨ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds,?_,geometry127_linked.2.2.2.2.1⟩
      change (ReferenceSensitivityData.CoarseLowerShape.Batch0015.cert127.cell.rProfile ReferenceProfileData.CoarseLowerShape.Batch0015.r127.bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true
      rw [←r_profile127_linked]
      exact List.all_eq_true.mp ReferenceProfileData.CoarseLowerShape.Batch0015.frames_checked _ (by simp only [ReferenceProfileData.CoarseLowerShape.Batch0015.profiles,List.mem_cons,List.mem_singleton]; tauto)
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Batch0015
